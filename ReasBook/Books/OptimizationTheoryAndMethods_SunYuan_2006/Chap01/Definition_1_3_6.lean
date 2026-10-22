/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Strong

-- Semantic recall hits verified for this item: `ConvexOn`, `StrictConvexOn`,
-- `StrongConvexOn`, `UniformConvexOn`, `ConcaveOn`, `StrictConcaveOn`,
-- `StrongConcaveOn`, and `UniformConcaveOn`.

section Definition136

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Chapter01 Definition 1.3.6 (1): for `S : Set E` and `f : E → ℝ`, convexity of `f`
on `S` is formalized by `ConvexOn ℝ S f`. The source's `ℝ^n` setting is a downstream
specialization of this canonical owner. -/
#check (ConvexOn ℝ : Set E → (E → ℝ) → Prop)

/- Chapter01 Definition 1.3.6 (2): strict convexity of `f` on `S` is formalized by
`StrictConvexOn ℝ S f`. -/
#check (StrictConvexOn ℝ : Set E → (E → ℝ) → Prop)

/- Chapter01 Definition 1.3.6 (3): uniform, equivalently strong, convexity of `f` on `S`
is formalized source-faithfully by the existence of a positive modulus `c` with
`StrongConvexOn S c f`. The primitive quadratic-modulus owner is `StrongConvexOn S c f`,
and mathlib's more general owner is `UniformConvexOn S φ f`. -/
#check (StrongConvexOn : Set E → ℝ → (E → ℝ) → Prop)
#check (UniformConvexOn : Set E → (ℝ → ℝ) → (E → ℝ) → Prop)

/-- The source-facing `∃ c > 0, StrongConvexOn S c f` formulation is exactly
quadratic-modulus uniform convexity. -/
theorem exists_pos_strongConvexOn_iff_exists_pos_uniformConvexOn (S : Set E) (f : E → ℝ) :
    (∃ c > 0, StrongConvexOn S c f) ↔
      ∃ c > 0, UniformConvexOn S (fun r ↦ c / 2 * r ^ (2 : ℕ)) f := by
  rfl

/- Chapter01 Definition 1.3.6 (4): concavity of `f` on `S` is formalized by
`ConcaveOn ℝ S f`. -/
#check (ConcaveOn ℝ : Set E → (E → ℝ) → Prop)

/- Chapter01 Definition 1.3.6 (5): strict concavity of `f` on `S` is formalized by
`StrictConcaveOn ℝ S f`. -/
#check (StrictConcaveOn ℝ : Set E → (E → ℝ) → Prop)

/- Chapter01 Definition 1.3.6 (6): uniform, equivalently strong, concavity of `f` on `S`
is formalized source-faithfully by the existence of a positive modulus `c` with
`StrongConcaveOn S c f`. The primitive quadratic-modulus owner is `StrongConcaveOn S c f`,
and mathlib's more general owner is `UniformConcaveOn S φ f`. -/
#check (StrongConcaveOn : Set E → ℝ → (E → ℝ) → Prop)
#check (UniformConcaveOn : Set E → (ℝ → ℝ) → (E → ℝ) → Prop)

/-- The source-facing `∃ c > 0, StrongConcaveOn S c f` formulation is exactly
quadratic-modulus uniform concavity. -/
theorem exists_pos_strongConcaveOn_iff_exists_pos_uniformConcaveOn (S : Set E) (f : E → ℝ) :
    (∃ c > 0, StrongConcaveOn S c f) ↔
      ∃ c > 0, UniformConcaveOn S (fun r ↦ c / 2 * r ^ (2 : ℕ)) f := by
  rfl

end Definition136
