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

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Definition 5.4.7.18 lies in the Chapter 5 positive-orthant / simplex-weighted moment domain.

Sampled owner declarations:
* `relativeDirection` in `Definition_5_4_7_14`, the source-facing scaled direction `δ_x(h)`;
* `Finset.centerMass` and `Finset.centerMass_eq_of_sum_1`, the canonical finite weighted-average
  owner and its sum-`1` bridge;
* `stdSimplex.sum_eq_one` and `stdSimplex.zero_le`, the canonical simplex facts needed for
  weighted means and nonnegativity.

Source/core/bridge triage:
* source-facing: `quantityS2`, the textbook weighted centered second moment of `δ_x(h)`;
* core/canonical: `Finset.univ.centerMass a (δ[x](h))` for the simplex-weighted mean;
* bridge/view: the explicit coordinate-sum formulas for the mean and for `quantityS2`.

Primitive data:
* simplex weights `a : Δ[n]`;
* a base point `x : Xₙ`;
* a direction `h : Eₙ`.

Derived API:
* the center-of-mass specialization `Finset.univ.centerMass a (δ[x](h))`;
* the coordinate bridge `centerMass_relativeDirection_eq_sum`;
* the source-facing quantity `quantityS2` and its sum/nonnegativity lemmas.

The previous version introduced a separate owner `weightedRelativeDirectionMean` for a notion
already owned by `Finset.centerMass`, and it used the raw subtype presentation of the strict
orthant. This refinement keeps the same `S₂` quantity, but reuses the chapter owner
`positiveOrthant n` and the canonical finite weighted-average owner for the auxiliary mean. -/

-- Proof sketch: `a` lies in the standard simplex, so its coordinates sum to `1`. Therefore the
-- center of mass with weights `a` is exactly the weighted coordinate sum.
/-- The simplex-weighted mean of the relative direction is the coordinate sum
`∑ i, a^(i) δ^(i)`. -/
theorem centerMass_relativeDirection_eq_sum
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    Finset.univ.centerMass a (δ[x](h)) =
      ∑ i : Fin n, a i * δ[x](h) i := by
  simpa [smul_eq_mul] using
    (show Finset.univ.centerMass a (δ[x](h)) = ∑ i : Fin n, a i • δ[x](h) i from
      Finset.univ.centerMass_eq_of_sum_1 (δ[x](h)) (stdSimplex.sum_eq_one a))

/-- Definition 5.4.7.18: the quantity `S₂` is the simplex-weighted second centered moment of the
relative direction `δ_x(h)`, centered by its simplex-weighted mean
`Finset.univ.centerMass a (δ[x](h))`. -/
def quantityS2 (a : Δ[n]) (x : Xₙ) (h : Eₙ) : ℝ :=
  a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i - Finset.univ.centerMass a (δ[x](h))) ^ (2 : ℕ)

-- Proof sketch: unfold `quantityS2`; the canonical dot-product notation `⬝ᵥ` is definitionally the
-- finite sum of the weighted squared centered coordinates.
/-- Evaluating `quantityS2` gives the textbook sum formula
`S₂ = ∑ i, a^(i) (δ^(i) - m)^2`, with `m = ⟪a, δ_x(h)⟫`. -/
theorem quantityS2_eq_sum
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    quantityS2 a x h =
      ∑ i : Fin n,
        a i * (δ[x](h) i - Finset.univ.centerMass a (δ[x](h))) ^ (2 : ℕ) := by
  rfl

-- Proof sketch: each simplex weight `a i` is nonnegative and each square
-- `(δ[x](h) i - Finset.univ.centerMass a (δ[x](h)))^2` is nonnegative, so every
-- summand in `quantityS2_eq_sum` is nonnegative and the finite sum is nonnegative.
/-- The quantity `S₂` is nonnegative. -/
theorem quantityS2_nonneg
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    0 ≤ quantityS2 a x h := by
  rw [quantityS2_eq_sum]
  refine Finset.sum_nonneg fun i _ ↦ ?_
  exact mul_nonneg (stdSimplex.zero_le a i) (by positivity)

end
