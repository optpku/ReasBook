/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open EuclideanSpace (positiveOrthant)

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Definition 5.4.7.14 lies in the Chapter 5 positive-orthant / coordinatewise-scaling domain.

Sampled owner declarations:
* `EuclideanSpace.positiveOrthant` from `Chap01/Definition_1_10_2`, the chapter owner for the
  strict positive orthant;
* `EuclideanSpace.mem_positiveOrthant_iff` from `Chap01/Definition_1_10_2`, the coordinatewise
  membership bridge for that owner;
* `WithLp.toLp` from mathlib, the canonical constructor from coordinate families into
  `EuclideanSpace`;
* `EuclideanSpace` as the ambient `PiLp 2` owner, whose coordinates are already accessed
  pointwise.

Best owner abstraction:
* source-facing: `relativeDirection x h`, the textbook relative direction `δ_x(h)`;
* core/canonical: the strict-orthant owner `positiveOrthant n` together with the canonical
  ambient `EuclideanSpace` constructor `WithLp.toLp`;
* bridge/view: the coordinate formula `δ[x](h) i = h i / x i`.

Primitive data:
* a base point `x : positiveOrthant n`;
* a direction `h : ℝⁿ`.

Derived API:
* the owner definition `relativeDirection`;
* the scoped notation `δ[x](h)` for the textbook relative direction `δ_x(h)`;
* the coordinate projection lemma `relativeDirection_apply`.

The previous version routed the source-facing owner through ad hoc local `Div` and `CoeFun`
instances. This refinement keeps the same mathematical object, but defines it directly by its
canonical coordinate formula in `EuclideanSpace`; the public bridge API is therefore the textbook
coordinate identity itself, with no hidden instance scaffolding. -/

/-- Definition 5.4.7.14: for a strictly positive point `x ∈ ℝ^n_{++}` and a direction `h ∈ ℝⁿ`,
the relative direction `δ_x(h)` is the vector whose `i`-th coordinate is `h^(i) / x^(i)`. -/
def relativeDirection (x : Xₙ) (h : Eₙ) : Eₙ :=
  WithLp.toLp 2 fun i ↦ h i / (x : Eₙ) i

namespace RelativeDirection

/- Source-facing Lean notation for the textbook relative direction `δ_x(h)`. -/
scoped notation:max "δ[" x "](" h ")" => relativeDirection x h

end RelativeDirection

open scoped RelativeDirection

-- Proof sketch: `relativeDirection` is defined by the coordinate formula
-- `WithLp.toLp 2 (fun i ↦ h i / x i)`, so evaluation at `i` is definitional.
/-- Evaluating `δ[x](h)` at `i` recovers the coordinate quotient `h^(i) / x^(i)`. -/
@[simp] theorem relativeDirection_apply (x : Xₙ) (h : Eₙ) (i : Fin n) :
    δ[x](h) i = h i / (x : Eₙ) i :=
  rfl

-- Proof sketch: extensionality reduces the vector equality to coordinates, where
-- `relativeDirection_apply` gives `0 / x i = 0`.
/-- The relative direction of the zero vector is zero. -/
@[simp] theorem relativeDirection_zero (x : Xₙ) :
    δ[x]((0 : Eₙ)) = 0 :=
  by
    ext i
    change 0 / (x : Eₙ) i = 0
    simp

-- Proof sketch: extensionality reduces to coordinates, where `relativeDirection_apply` turns the
-- statement into `(h₁ i + h₂ i) / x i = h₁ i / x i + h₂ i / x i`.
/-- The relative direction is additive in the ambient direction argument. -/
theorem relativeDirection_add (x : Xₙ) (h₁ h₂ : Eₙ) :
    δ[x]((h₁ + h₂)) = δ[x](h₁) + δ[x](h₂) :=
  by
    ext i
    change (h₁ i + h₂ i) / (x : Eₙ) i = h₁ i / (x : Eₙ) i + h₂ i / (x : Eₙ) i
    rw [add_div]

-- Proof sketch: extensionality reduces to coordinates, where `relativeDirection_apply` turns the
-- statement into `(t * h i) / x i = t * (h i / x i)`.
/-- The relative direction commutes with scalar multiplication in the ambient direction. -/
theorem relativeDirection_smul (x : Xₙ) (t : ℝ) (h : Eₙ) :
    δ[x]((t • h)) = t • δ[x](h) :=
  by
    ext i
    change (t * h i) / (x : Eₙ) i = t * (h i / (x : Eₙ) i)
    rw [mul_div_assoc]

end
