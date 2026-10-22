/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_4_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators EuclideanOrthant SecondOrderCone

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

noncomputable local instance instFintypeFinDefinition5471 : Fintype (Fin 2) :=
  Fintype.ofFinite (Fin 2)

/- Definition 5.4.7.1 lies in the Chapter 5 power-cone / cone-composition domain.

Sampled owner declarations:
* `coneCompositionFeasibleSet` and `mem_coneCompositionFeasibleSet_iff` from
  `Definition_5_4_6_3`, the chapter owner for feasible sets cut out by a cone-order comparison;
* `EuclideanSpace.nonnegativeOrthant` and `EuclideanSpace.mem_nonnegativeOrthant_iff` from
  `Chap01/Definition_1_10_2`, the canonical owner/view for `ℝ_+^2`;
* `standardLogarithmicBarrierAmbient` from `Definition_5_4_3_2`, the chapter ambient bridge for
  the standard orthant logarithmic barrier;
* `secondOrderCone` and `mem_secondOrderCone_iff` from `Lemma_5_4_3_3`, the canonical owner/view
  for the planar cone `\{(z, y) \mid |z| ≤ y\}`;
* `Prod.swap`, the canonical bridge between the source `(y, z)` coordinates and the owner
  `(z, y)` coordinates.

Source/core/bridge triage:
* source-facing: `powerCone α`, the textbook power cone `K_α`;
* core/canonical: `coneCompositionFeasibleSet`, `ℝ₊^2`, and
  `standardLogarithmicBarrierAmbient 2`;
* bridge/view: the private coordinate bridge `powerConePairToEuclidean` together with
  `mem_powerConeQ1_iff`, `powerConeBarrier_apply`, and `mem_powerCone_iff`.

Primitive data:
* the weighted geometric mean `powerConeGeometricMean α`;
* the scalar positive cone `ConvexCone.positive ℝ ℝ`.

Derived API:
* the orthant `powerConeQ1 = ℝ_+²`, pulled back from the canonical owner `ℝ₊^2`;
* the planar comparison set `powerConeQ2`, viewed as the swapped-coordinate second-order cone;
* the orthant barrier `powerConeBarrier`, pulled back from
  `standardLogarithmicBarrierAmbient 2`;
* the barrier parameter `powerConeBarrierParameter`;
* the pointwise evaluation and membership lemmas below.

The scalar cone `K = ℝ_+` is already canonically owned by `ConvexCone.positive ℝ ℝ`, the orthant
`Q₁ = ℝ_+²` by `ℝ₊^2`, and its logarithmic barrier by `standardLogarithmicBarrierAmbient 2`,
while the comparison cone `Q₂ = {(y, z) | y ≥ |z|}` is the coordinate-swapped view of the
Chapter 5 second-order cone owner. This file therefore keeps the textbook owner `powerCone α`,
but makes its pair-level orthant and barrier data thin coordinate bridges to those earlier
owners instead of repeating the raw coordinate model as parallel primitive declarations. -/

private def powerConePairToEuclidean : ℝ × ℝ → E₂ :=
  fun x ↦ WithLp.toLp 2 ![x.1, x.2]

private theorem neg_sum_log_pair_eq (x₁ x₂ : ℝ) :
    -(∑ x : Fin 2, Real.log (![x₁, x₂] x)) = -Real.log x₁ - Real.log x₂ := by
  have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by
    ext i
    constructor
    · intro _
      have hi : i = 0 ∨ i = 1 := by
        omega
      simp [hi]
    · intro _
      simp
  have hsum : (∑ x : Fin 2, Real.log (![x₁, x₂] x)) = Real.log x₁ + Real.log x₂ := by
    simp [huniv]
  have hneg : -(∑ x : Fin 2, Real.log (![x₁, x₂] x)) = -(Real.log x₁ + Real.log x₂) :=
    congrArg (fun s : ℝ ↦ -s) hsum
  calc
    -(∑ x : Fin 2, Real.log (![x₁, x₂] x)) = -(Real.log x₁ + Real.log x₂) := hneg
    _ = -Real.log x₁ - Real.log x₂ := by
      ring

/-- The weighted geometric mean `x₁^α x₂^(1 - α)` that appears in the power-cone representation;
this is the scalar map `ξ`. -/
def powerConeGeometricMean (α : ℝ) (x : ℝ × ℝ) : ℝ :=
  Real.rpow x.1 α * Real.rpow x.2 (1 - α)

namespace PowerConeGeometricMean

/- Source-facing Lean notation for the textbook weighted geometric mean `ξ`. -/
scoped notation:max "ξ[" α:arg "]" => powerConeGeometricMean α

end PowerConeGeometricMean

open scoped PowerConeGeometricMean

-- Proof sketch: unfold `ξ[α]`.
/-- Evaluating `ξ[α]` at `(x₁, x₂)` gives the product
`x₁^α x₂^(1 - α)` written using `Real.rpow`. -/
theorem powerConeGeometricMean_apply (α x₁ x₂ : ℝ) :
    ξ[α] (x₁, x₂) =
      Real.rpow x₁ α * Real.rpow x₂ (1 - α) :=
  rfl

/-- The orthant `Q₁ = ℝ_+²` used in the power-cone representation, pulled back from the
canonical Euclidean orthant owner along the source coordinate bridge. -/
abbrev powerConeQ1 : Set (ℝ × ℝ) :=
  powerConePairToEuclidean ⁻¹' (ℝ₊^2 : Set E₂)

-- Proof sketch: rewrite through the canonical orthant owner `ℝ₊^2` and its coordinatewise
-- membership theorem.
/-- A point `(x₁, x₂)` belongs to `powerConeQ1` exactly when both coordinates are nonnegative. -/
theorem mem_powerConeQ1_iff (x₁ x₂ : ℝ) :
    (x₁, x₂) ∈ powerConeQ1 ↔ 0 ≤ x₁ ∧ 0 ≤ x₂ := by
  simp [powerConeQ1, powerConePairToEuclidean, EuclideanSpace.mem_nonnegativeOrthant_iff]

/-- The set `Q₂ = {(y, z) ∈ ℝ × ℝ : y ≥ |z|}` used in the power-cone representation. It is the
`(y, z)`-coordinate view of the canonical second-order cone on `ℝ × ℝ`. -/
abbrev powerConeQ2 : Set (ℝ × ℝ) :=
  Prod.swap ⁻¹' (K₂[ℝ] : Set (ℝ × ℝ))

-- Proof sketch: rewrite through the swapped-coordinate second-order cone owner and then apply
-- `mem_secondOrderCone_iff`.
/-- A pair `(y, z)` belongs to `powerConeQ2` exactly when `y ≥ |z|`. -/
theorem mem_powerConeQ2_iff (y z : ℝ) :
    (y, z) ∈ powerConeQ2 ↔ y ≥ |z| := by
  change (z, y) ∈ K₂[ℝ] ↔ y ≥ |z|
  rw [mem_secondOrderCone_iff]
  simp [Real.norm_eq_abs, ge_iff_le]

/-- Definition 5.4.7.1: for `α ∈ (0, 1)`, the power cone `K_α` consists of the triples
`((x₁, x₂), z)` with `(x₁, x₂) ∈ ℝ_+²` and `|z| ≤ x₁^α x₂^(1 - α)`. The companion declarations
below record the associated representation data `Q₁`, `F`, `ν`, `K`, `ξ`, and `Q₂`. -/
def powerCone (α : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  coneCompositionFeasibleSet
    powerConeQ1
    (ConvexCone.positive ℝ ℝ)
    ξ[α]
    powerConeQ2

namespace PowerCone

/- Source-facing Lean notation for the textbook power cone `K_α`. -/
scoped notation:max "K_[" α:arg "]" => powerCone α

end PowerCone

open scoped PowerCone

-- Proof sketch: expand the owner specialization `powerCone α` through
-- `mem_coneCompositionFeasibleSet_iff`. The comparison witness `y` satisfies
-- `|z| ≤ y ≤ x₁^α x₂^(1 - α)`, and conversely `y = |z|` realizes the owner constraints.
/-- A triple `((x₁, x₂), z)` belongs to `K_[α]` exactly when `x₁, x₂ ≥ 0` and
`|z| ≤ x₁^α x₂^(1 - α)`. -/
theorem mem_powerCone_iff (α x₁ x₂ z : ℝ) :
    ((x₁, x₂), z) ∈ K_[α] ↔
      0 ≤ x₁ ∧ 0 ≤ x₂ ∧ |z| ≤ ξ[α] (x₁, x₂) := by
  rw [powerCone, mem_coneCompositionFeasibleSet_iff]
  constructor
  · rintro ⟨y, hx, hy, hz⟩
    have hx' : 0 ≤ x₁ ∧ 0 ≤ x₂ := (mem_powerConeQ1_iff x₁ x₂).1 (by simpa using hx)
    have hy' : y ≤ ξ[α] (x₁, x₂) := by
      rw [ConvexCone.mem_positive] at hy
      exact sub_nonneg.mp (by simpa using hy)
    have hz' : |z| ≤ y := (mem_powerConeQ2_iff y z).1 (by simpa using hz)
    exact ⟨hx'.1, hx'.2, le_trans hz' hy'⟩
  · rintro ⟨hx₁, hx₂, hz⟩
    refine ⟨|z|, (mem_powerConeQ1_iff x₁ x₂).2 ⟨hx₁, hx₂⟩, ?_, ?_⟩
    · rw [ConvexCone.mem_positive]
      exact sub_nonneg.mpr hz
    · exact (mem_powerConeQ2_iff |z| z).2 le_rfl

/-- The logarithmic barrier `F(x) = -log x₁ - log x₂` on the interior of `Q₁ = ℝ_+²`, obtained
by pulling back the canonical positive-orthant ambient barrier along the source coordinate
bridge. -/
def powerConeBarrier : (ℝ × ℝ) → ℝ :=
  standardLogarithmicBarrierAmbient 2 ∘ powerConePairToEuclidean

-- Proof sketch: unfold `powerConeBarrier` through the canonical ambient orthant barrier and
-- simplify the `Fin 2` sum back to the two-coordinate formula.
/-- Evaluating `powerConeBarrier` at `(x₁, x₂)` gives the textbook formula
`-log x₁ - log x₂`. -/
theorem powerConeBarrier_apply (x₁ x₂ : ℝ) :
    powerConeBarrier (x₁, x₂) = -Real.log x₁ - Real.log x₂ :=
  by
    simpa [powerConeBarrier, powerConePairToEuclidean, standardLogarithmicBarrierAmbient,
      Function.comp_apply] using neg_sum_log_pair_eq x₁ x₂

/-- The barrier parameter `ν = 2` attached to the orthant barrier in the power-cone
representation. -/
def powerConeBarrierParameter : NNReal :=
  2

-- Proof sketch: unfold `powerConeBarrierParameter`.
/-- The power-cone representation uses barrier parameter `ν = 2`. -/
theorem powerConeBarrierParameter_eq :
    powerConeBarrierParameter = 2 :=
  rfl
