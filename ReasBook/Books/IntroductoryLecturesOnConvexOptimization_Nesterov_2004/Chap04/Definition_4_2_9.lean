/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Text_4_2_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open LinearMap (BilinForm)
open scoped BInducedNorm

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 4.2.9 is source-facing in the chapter's `B`-induced norm geometry.

Sampled owner-style declarations:
- `powerDistance` in `Text_4_2_6`
- `powerDistance_apply` in `Text_4_2_6`
- the notation layer `‖x‖[B]` from `Definition_4_3_4`

Best owner abstraction:
- source-facing: the degree-`p` power function centered at `x₀` in the `B`-induced geometry
- core/canonical: the public owner carrier `LinearMap.BilinForm.PrimalSpace B`, equipped with the
  norm and inner product induced by `B`
- bridge/view: the earlier chapter owner `powerDistance p x₀` on that intrinsic carrier

Primitive data:
- `B : BilinForm ℝ E`
- `p : ℝ`
- `x₀ : E`

Derived API:
- the intrinsic carrier `LinearMap.BilinForm.PrimalSpace B`
- the induced norm `‖x‖[B]`, now realized as the ambient norm on `PrimalSpace B`
- the source-facing owner `powerFunction B p x₀`
- the pointwise formula `x ↦ (1 / p) * ‖x - x₀‖[B]^p`

The public owner therefore stays the source-facing `B`-power function, but it now lives on the
intrinsic `B`-weighted carrier and reuses the earlier chapter owner `powerDistance` there instead
of rebuilding the `B`-normed-space structure privately.
-/
namespace LinearMap.BilinForm

/-- The carrier `E`, equipped with the norm induced by the symmetric positive-definite bilinear
form owner `B`. -/
abbrev PrimalSpace (_B : BilinForm ℝ E) := E

/-- The additive norm induced on the carrier `PrimalSpace B` by the primal seminorm of `B`. -/
def primalAddGroupNorm
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef] :
    AddGroupNorm (PrimalSpace B) :=
  let p : Seminorm ℝ E := B.primalSeminorm Fact.out
  { toFun := p
    map_zero' := map_zero p
    add_le' := map_add_le_add p
    neg' := map_neg_eq_map p
    eq_zero_of_map_eq_zero' := fun _ hx ↦
      let _ : Seminorm.IsNorm p := B.primalSeminorm_isNorm Fact.out
      Seminorm.IsNorm.eq_zero_of_map_eq_zero hx }

instance (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef] :
    NormedAddCommGroup (PrimalSpace B) :=
  AddGroupNorm.toNormedAddCommGroup (primalAddGroupNorm B)

instance (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef] :
    NormedSpace ℝ (PrimalSpace B) :=
  { norm_smul_le := fun a x ↦ by
      let p : Seminorm ℝ E := B.primalSeminorm Fact.out
      change p (a • x) ≤ ‖a‖ * p x
      exact le_of_eq (p.smul' a x) }

/-- On the intrinsic carrier `PrimalSpace B`, the ambient norm is exactly the chapter notation
`‖·‖[B]`. -/
@[simp] theorem primalSpace_norm_eq_bInducedNorm
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef] (x : PrimalSpace B) :
    ‖x‖ = B.primalSeminorm Fact.out x :=
  rfl

end LinearMap.BilinForm

/-- Definition 4.2.9: for a fixed center `x₀` and a positive-definite self-adjoint bilinear form
`B`, the degree-`p` power function is `x ↦ (1 / p) * ‖x - x₀‖[B]^p`. -/
def powerFunction (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef] (p : ℝ)
    (x0 : LinearMap.BilinForm.PrimalSpace B) : LinearMap.BilinForm.PrimalSpace B → ℝ :=
  powerDistance p x0

/-- Evaluating `powerFunction B p x₀` at `x` gives `(1 / p) * ‖x - x₀‖^p` in the intrinsic
`B`-weighted norm on `PrimalSpace B`. -/
theorem powerFunction_apply (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef] (p : ℝ)
    (x0 x : LinearMap.BilinForm.PrimalSpace B) :
    powerFunction B p x0 x = (1 / p) * Real.rpow ‖x - x0‖ p := by
  rfl
