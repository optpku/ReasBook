/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {Q : Type u}

/- Definition 3.1.2.3 lies in the chapter's two-function minimax-linearization domain.

Sampled owner-style declarations:
- mathlib `unitInterval`, the canonical owner of the parameter set `[0, 1]`
- mathlib `AffineMap.lineMap`, the canonical affine-combination owner
- mathlib `AffineMap.lineMap_apply_ring`, the textbook scalar formula
- mathlib `sInf`, the canonical infimum owner for the corresponding `EReal` value sets

Best owner abstraction:
- source-facing owner: `IsMinimaxLinearizationParameter`

Primitive data:
- a common domain `Q`
- two real-valued functions `f₁ f₂ : Q → ℝ`
- a parameter `lam : unitInterval`

Derived API:
- the companion specification theorem `isMinimaxLinearizationParameter_iff`

Source/core/bridge triage:
- source-facing: the textbook minimax-linearization parameter condition
- core/canonical: `unitInterval`, `AffineMap.lineMap`, and `sInf`
- bridge/view: the displayed `EReal`-infimum equality recorded by the companion theorem

No earlier chapter owner packages this notion more canonically, so this file keeps the
source-facing predicate as the owner and reuses mathlib's affine-combination surface inside that
owner instead of duplicating the scalar formula directly. -/

/-- Definition 3.1.2.3: a minimax linearization parameter for `f₁, f₂ : Q → ℝ` is a scalar
`lam ∈ [0, 1]` such that the extended-real infimum of the pointwise maximum
`x ↦ max (f₁ x) (f₂ x)` equals the extended-real infimum of the affine combination
`x ↦ lam * f₁ x + (1 - lam) * f₂ x`. -/
def IsMinimaxLinearizationParameter
    (f₁ f₂ : Q → ℝ) (lam : unitInterval) : Prop :=
  sInf (Set.range fun x ↦ ((max (f₁ x) (f₂ x) : ℝ) : EReal)) =
    sInf (Set.range fun x ↦ ((AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ) : ℝ) : EReal))

/-- Unfolding the minimax-linearization predicate gives the displayed equality of extended-real
infima. -/
-- Proof sketch: this is the defining specification of `IsMinimaxLinearizationParameter`, so the
-- result follows by unfolding the definition.
@[simp] theorem isMinimaxLinearizationParameter_iff
    (f₁ f₂ : Q → ℝ) (lam : unitInterval) :
    IsMinimaxLinearizationParameter f₁ f₂ lam ↔
      sInf (Set.range fun x ↦ ((max (f₁ x) (f₂ x) : ℝ) : EReal)) =
        sInf (Set.range fun x ↦ ((AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ) : ℝ) : EReal)) :=
  Iff.rfl
