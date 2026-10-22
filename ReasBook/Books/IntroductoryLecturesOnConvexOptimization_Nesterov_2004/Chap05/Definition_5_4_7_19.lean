/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators RelativeDirection StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Definition 5.4.7.19 is a source-facing centered-moment item in the chapter's positive-orthant /
simplex-weighted moment domain.

Sampled owner declarations:
* `relativeDirection` in `Definition_5_4_7_14`, the source-facing scaled direction `δ_x(h)`;
* `Finset.centerMass` and `Finset.centerMass_eq_of_sum_1`, the canonical finite weighted-average
  owner and its sum-`1` bridge;
* mathlib `dotProduct` / `⬝ᵥ`, the canonical owner for finite weighted sums of coordinatewise
  products;
* `quantityS2` in `Definition_5_4_7_18`, the immediately preceding source-facing weighted centered
  second moment built from the same owner data.

Best owner abstraction:
* source-facing: `quantityS3`, the weighted third centered moment of the relative direction
  `δ_x(h)`;
* core/canonical: `Finset.univ.centerMass a (δ[x](h))` for the simplex-weighted mean together
  with the `dotProduct` specialization
  `a ⬝ᵥ fun i ↦ (δ[x](h) i - Finset.univ.centerMass a (δ[x](h)))^3`;
* bridge/view: the explicit finite-sum expansion.

Primitive data:
* simplex weights `a : Δ[n]`;
* a base point `x : Xₙ`;
* a direction `h : Eₙ`.

Derived API:
* the center-of-mass specialization `Finset.univ.centerMass a (δ[x](h))`;
* the coordinate formula
  `S₃ = ∑ i, a i * (δ[x](h) i - Finset.univ.centerMass a (δ[x](h)))^3`.

The previous version exposed an auxiliary vector `delta` and center `m` as primitive data even
though the surrounding subsection canonically obtains both from `x`, `h`, and `a`. This
refinement keeps the same mathematical quantity `S₃`, but places it on the same source-facing
owner layer as `quantityS2`, with the mean derived canonically by `Finset.centerMass`.
-/

/-- Definition 5.4.7.19: the quantity `S₃` is the simplex-weighted third centered moment of the
relative direction `δ_x(h)`, centered by its simplex-weighted mean
`Finset.univ.centerMass a (δ[x](h))`. -/
def quantityS3 (a : Δ[n]) (x : Xₙ) (h : Eₙ) : ℝ :=
  a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i - Finset.univ.centerMass a (δ[x](h))) ^ (3 : ℕ)

-- Proof sketch: unfold `quantityS3`; the canonical dot-product notation `⬝ᵥ` is definitionally the
-- finite sum of the weighted cubed centered coordinates.
/-- Expanding `quantityS3` gives the coordinate formula
`S₃ = ∑ i, a^(i) (δ^(i) - m)^3`, with `m = Finset.univ.centerMass a (δ[x](h))`. -/
theorem quantityS3_eq_sum (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    quantityS3 a x h =
      ∑ i : Fin n,
        a i * (δ[x](h) i - Finset.univ.centerMass a (δ[x](h))) ^ (3 : ℕ) :=
  rfl

end
