/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_23

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open Module LinearMap
open scoped BInducedNorm Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Definition 5.0.20 lies in the local Hessian-metric / dual-norm domain.

Sampled owner declarations:
* `hessian` in `Chap01/Definition_1_4_16`, the canonical Hessian operator owner;
* `LinearMap.BilinForm.dualNorm` and `dualNorm_apply_strongDual` in `Chap04/Definition_4_2_6`,
  the canonical dual norm attached to a symmetric positive-definite bilinear form;
* `ContinuousLinearMap.IsInvertible` and `ContinuousLinearMap.inverse` in mathlib, the canonical
  owner and inverse bridge for a nondegenerate Hessian operator;
* `HasPositiveDefiniteHessianOn` together with
  `HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem` and
  `HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem` in `Definition_5_0_23`, the
  domain-level owner and its canonical bridge to the local Hessian data needed here.

Best owner abstraction:
* source-facing: the Hessian-metric dual local norm of a covector at `x`;
* core/canonical: the bilinear-form owner `‖g‖[hessianBilin f x,*]`;
* bridge/view: the canonical inverse `((hessian f x).inverse : E →L[ℝ] E)`.

Primitive data:
* a function `f`;
* a base point `x`;
* positivity of the Hessian operator at `x`;
* an invertibility witness for that Hessian;
* a covector `g`.

Derived API:
* the source-facing notation `‖g‖*[f; x | hPos; hInv]`;
* the determinant bridge `HessianDualLocalNorm.ofDetNeZero`;
* the domain-level bridge `HessianDualLocalNorm.ofPosDefMem`;
* the inverse-Hessian pairing formula for that dual norm;
* nonnegative scalar homogeneity of the dual local norm.

This file keeps the textbook dual local norm as the source-facing owner, but refines it to the
canonical Chapter 4 dual norm attached to the positive-definite Hessian bilinear form rather than
to a determinant-based witness. Determinant nonvanishing remains only as a thin bridge to the
canonical owner `ContinuousLinearMap.IsInvertible`. -/

/-- The bilinear form on `E` induced by the Hessian operator of `f` at `x`. -/
private def hessianBilin (f : E → ℝ) (x : E) : LinearMap.BilinForm ℝ E :=
  ((innerSL ℝ).comp (hessian f x)).toBilinForm

/-- Evaluating `hessianBilin f x` on `u` and `v` pairs `v` with the Hessian of `f` at `x`
applied to `u`. -/
private theorem hessianBilin_apply (f : E → ℝ) (x u v : E) :
    hessianBilin f x u v = inner ℝ (hessian f x u) v :=
  rfl

/-- A positive Hessian operator induces a symmetric Hessian bilinear form. -/
private theorem hessianBilin_isSymm_of_isPositive {f : E → ℝ} {x : E}
    (hPos : (hessian f x).IsPositive) : (hessianBilin f x).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  intro u v
  change inner ℝ (hessian f x u) v = inner ℝ (hessian f x v) u
  simpa [real_inner_comm] using hPos.isSymmetric u v

/-- A positive invertible Hessian operator induces a positive-definite Hessian bilinear form. -/
private theorem hessianBilin_posDef_of_isPositive_of_isInvertible {f : E → ℝ} {x : E}
    (hPos : (hessian f x).IsPositive) (hInv : (hessian f x).IsInvertible) :
    (hessianBilin f x).toQuadraticMap.PosDef := by
  rw [QuadraticMap.posDef_iff_nonneg]
  refine ⟨?_, ?_⟩
  · intro u
    change 0 ≤ inner ℝ (hessian f x u) u
    simpa [real_inner_comm] using hPos.inner_nonneg_right u
  · intro u hu
    change inner ℝ (hessian f x u) u = 0 at hu
    have hHu : hessian f x u = 0 := by
      obtain ⟨m, w, hA⟩ := (ContinuousLinearMap.isPositive_iff_eq_sum_rankOne).mp hPos
      rw [hA] at hu ⊢
      have hsum : ∑ j : Fin m, (inner ℝ (w j) u) ^ (2 : ℕ) = 0 := by
        simpa [Finset.sum_apply, InnerProductSpace.rankOne_apply, sum_inner, real_inner_smul_left,
          pow_two] using hu
      have hw : ∀ i : Fin m, inner ℝ (w i) u = 0 := by
        intro i
        exact sq_eq_zero_iff.mp <|
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun j _ ↦ sq_nonneg (inner ℝ (w j) u))).mp hsum i (by simp)
      simp [Finset.sum_apply, InnerProductSpace.rankOne_apply, hw]
    apply hInv.injective
    simpa using hHu

/-- A Hessian with nonzero determinant is canonically invertible as a continuous linear map. -/
theorem hessian_isInvertible_of_det_ne_zero {f : E → ℝ} {x : E}
    (hH : (hessian f x).det ≠ 0) : (hessian f x).IsInvertible :=
  ⟨(hessian f x).toContinuousLinearEquivOfDetNeZero hH, rfl⟩

-- Internal bridge used to specialize the Chapter 4 `B.toDual` inverse-pairing formula to the
-- Hessian bilinear form. Keeping it private avoids exposing bridge data as public theorem-statement
-- scaffolding.
private theorem hessianBilin_dualPreimage_eq_inverse {f : E → ℝ} {x : E}
    (hPos : (hessian f x).IsPositive) (hInv : (hessian f x).IsInvertible)
    (g : StrongDual ℝ E) :
    (hessianBilin f x).dualPreimage
        (hessianBilin_posDef_of_isPositive_of_isInvertible hPos hInv) g.toLinearMap =
      (hessian f x).inverse ((toDual ℝ E).symm g) := by
  let B := hessianBilin f x
  let hBPos : B.toQuadraticMap.PosDef :=
    hessianBilin_posDef_of_isPositive_of_isInvertible hPos hInv
  let hnd : (hessianBilin f x).Nondegenerate :=
    B.nondegenerate_of_posDef hBPos
  apply (B.toDual hnd).injective
  ext u
  calc
    B (B.dualPreimage hBPos g.toLinearMap) u =
        g u := by
      exact B.dualPreimage_apply hBPos g.toLinearMap u
    _ =
        ((B.toDual hnd) ((hessian f x).inverse ((toDual ℝ E).symm g))) u := by
      have hinv :
          (hessian f x) ((hessian f x).inverse ((toDual ℝ E).symm g)) =
            (toDual ℝ E).symm g :=
        hInv.self_apply_inverse ((toDual ℝ E).symm g)
      let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
      rw [LinearMap.BilinForm.toDual_def, hessianBilin_apply, hinv]
      simp

/-- Definition 5.0.20: when the Hessian of `f` at `x` is positive and invertible, the dual
local norm of a covector `g` is the Chapter 4 dual norm attached to the Hessian bilinear form. -/
abbrev dualLocalNorm (f : E → ℝ) (x : E) (hPos : (hessian f x).IsPositive)
    (hInv : (hessian f x).IsInvertible) (g : StrongDual ℝ E) : ℝ :=
  let _ : Fact (hessianBilin f x).IsSymm := ⟨hessianBilin_isSymm_of_isPositive hPos⟩
  let _ : Fact (hessianBilin f x).toQuadraticMap.PosDef :=
    ⟨hessianBilin_posDef_of_isPositive_of_isInvertible hPos hInv⟩
  (hessianBilin f x).dualNorm Fact.out g.toLinearMap

namespace HessianDualLocalNorm

/-- Source-facing notation for the Hessian-metric dual local norm of `g` at `x`. -/
scoped notation:max "‖" g "‖*[" f "; " x " | " hPos "; " hInv "]" =>
  dualLocalNorm f x hPos hInv g

/-- When the Hessian is given to be positive and determinant-nondegenerate, the dual local norm is
obtained by passing through the canonical invertibility owner. -/
abbrev ofDetNeZero (f : E → ℝ) (x : E) (hPos : (hessian f x).IsPositive)
    (hH : (hessian f x).det ≠ 0) (g : StrongDual ℝ E) : ℝ :=
  dualLocalNorm f x hPos (hessian_isInvertible_of_det_ne_zero hH) g

/-- When `f` has positive-definite Hessian on `dom`, the dual local norm at `x ∈ dom` is obtained
from the canonical positivity and invertibility bridges supplied by that owner. -/
abbrev ofPosDefMem (f : E → ℝ) {dom : Set E} {x : E}
    [HasPositiveDefiniteHessianOn dom f] (hx : x ∈ dom) (g : StrongDual ℝ E) : ℝ :=
  dualLocalNorm f x
    (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hx)
    (hessian_isInvertible_of_det_ne_zero
      (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx)) g

end HessianDualLocalNorm

open scoped HessianDualLocalNorm

-- Proof sketch: specialize the Chapter 4 `B`-dual norm formula to the Hessian bilinear form, then
-- identify the `B.toDual` inverse image with the inverse Hessian applied to the Riesz vector.
/-- Expanding `‖g‖*[f; x | hPos; hInv]` gives the square root of the inverse-Hessian pairing of the
covector `g` with itself at `x`. -/
theorem dualLocalNorm_def (f : E → ℝ) (x : E) (hPos : (hessian f x).IsPositive)
    (hInv : (hessian f x).IsInvertible) (g : StrongDual ℝ E) :
    ‖g‖*[f; x | hPos; hInv] =
      Real.sqrt (g ((hessian f x).inverse ((toDual ℝ E).symm g))) := by
  let hSymm : (hessianBilin f x).IsSymm := hessianBilin_isSymm_of_isPositive hPos
  let hBPos : (hessianBilin f x).toQuadraticMap.PosDef :=
    hessianBilin_posDef_of_isPositive_of_isInvertible hPos hInv
  calc
    ‖g‖*[f; x | hPos; hInv] =
        Real.sqrt (g ((hessianBilin f x).dualPreimage hBPos g.toLinearMap)) := by
      simpa [dualLocalNorm, hSymm, hBPos] using
        (LinearMap.BilinForm.dualNorm_apply_strongDual (hessianBilin f x) hSymm hBPos g)
    _ =
        Real.sqrt (g ((hessian f x).inverse ((toDual ℝ E).symm g))) := by
      congr 1
      simpa using congrArg g (hessianBilin_dualPreimage_eq_inverse hPos hInv g)

/-- The Hessian-metric dual local norm is always nonnegative. -/
theorem dualLocalNorm_nonneg (f : E → ℝ) (x : E) (hPos : (hessian f x).IsPositive)
    (hInv : (hessian f x).IsInvertible) (g : StrongDual ℝ E) :
    0 ≤ ‖g‖*[f; x | hPos; hInv] := by
  rw [dualLocalNorm_def]
  exact Real.sqrt_nonneg _

/-- The Hessian-metric dual local norm is positively homogeneous for nonnegative scalar multiples
of covectors. -/
theorem dualLocalNorm_smul_nonneg (f : E → ℝ) (x : E) (hPos : (hessian f x).IsPositive)
    (hInv : (hessian f x).IsInvertible) (g : StrongDual ℝ E) {a : ℝ} (ha : 0 ≤ a) :
    ‖a • g‖*[f; x | hPos; hInv] = a * ‖g‖*[f; x | hPos; hInv] := by
  let B := hessianBilin f x
  let hSymm : B.IsSymm := hessianBilin_isSymm_of_isPositive hPos
  let hBPos : B.toQuadraticMap.PosDef :=
    hessianBilin_posDef_of_isPositive_of_isInvertible hPos hInv
  let z := B.dualPreimage hBPos g.toLinearMap
  have hz : 0 ≤ B z z := hBPos.nonneg z
  have hz' : 0 ≤ g z := by
    simpa [z] using hz
  calc
    ‖a • g‖*[f; x | hPos; hInv] =
        Real.sqrt ((a • g) (B.dualPreimage hBPos ((a • g : StrongDual ℝ E).toLinearMap))) := by
      simpa [dualLocalNorm, B, hSymm, hBPos] using
        (LinearMap.BilinForm.dualNorm_apply_strongDual B hSymm hBPos (a • g : StrongDual ℝ E))
    _ = Real.sqrt ((a * a) * g z) := by
      simp [LinearMap.BilinForm.dualPreimage, z, map_smul, smul_eq_mul]
      ring_nf
    _ = Real.sqrt (a * a) * Real.sqrt (g z) := by
      rw [Real.sqrt_mul (mul_nonneg ha ha) (g z)]
    _ = a * Real.sqrt (g z) := by
      rw [Real.sqrt_mul_self ha]
    _ = a * ‖g‖*[f; x | hPos; hInv] := by
      congr 1
      symm
      simpa [dualLocalNorm, B, hSymm, hBPos, z] using
        (LinearMap.BilinForm.dualNorm_apply_strongDual B hSymm hBPos g)

namespace HessianDualLocalNorm

/-- Expanding `HessianDualLocalNorm.ofDetNeZero f x hPos hH g` recovers the inverse-Hessian
pairing formula through the determinant-to-invertibility bridge. -/
@[simp] theorem ofDetNeZero_def (f : E → ℝ) (x : E) (hPos : (hessian f x).IsPositive)
    (hH : (hessian f x).det ≠ 0) (g : StrongDual ℝ E) :
    ofDetNeZero f x hPos hH g =
      Real.sqrt
        (g ((hessian f x).inverse ((toDual ℝ E).symm g))) := by
  simp [ofDetNeZero, dualLocalNorm_def]

/-- Expanding `HessianDualLocalNorm.ofPosDefMem f hx g` recovers the inverse-Hessian pairing
formula with the local Hessian data derived from positive definiteness on `dom`. -/
@[simp] theorem ofPosDefMem_def (f : E → ℝ) {dom : Set E} {x : E}
    [HasPositiveDefiniteHessianOn dom f] (hx : x ∈ dom) (g : StrongDual ℝ E) :
    ofPosDefMem f hx g =
      Real.sqrt
        (g ((hessian f x).inverse ((toDual ℝ E).symm g))) := by
  simp [ofPosDefMem, dualLocalNorm_def]

end HessianDualLocalNorm

end
