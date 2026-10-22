/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Definition 4.2.11 lies in Chapter 4's higher-order conditioning domain.

Sampled owner-style declarations:
* project `f ∈ 𝒞^{p - 1,p - 1}_{L}(s)` in `Definition_4_2_10`
* project `uniformConvexPowerModulus` in `Definition_4_2_8`
* mathlib `LipschitzWith`
* mathlib `UniformConvexOn`

Best owner abstraction:
* source-facing: the global quantities `σ_p(f)`, `L_p(f)`, and `γ_p(f)`
* core/canonical: `f ∈ 𝒞^{p - 1,p - 1}_{L}(Set.univ)` together with
  `UniformConvexOn Set.univ (uniformConvexPowerModulus σ p) f`
* source-facing finiteness owner: `HasIteratedFDerivLipschitzConstantOfDegree p f`
* bridge/view: the source-style whole-space iterated-derivative norm estimate recovered from the
  `Set.univ` owner in `Definition_4_2_10`

Primitive data:
* whole-space degree-`p` uniform convexity, already owned by `UniformConvexOn`
* whole-space degree-`p` iterated-derivative Lipschitz control, already owned upstream by the
  `Set.univ` specialization `f ∈ 𝒞^{p - 1,p - 1}_{L}(Set.univ)` with `L : NNReal`
* finiteness of that control, recorded directly by the owner class
  `HasIteratedFDerivLipschitzConstantOfDegree p f`
* finiteness of the degree-`p` uniform-convexity parameter, recorded by the owner class
  `HasUniformConvexityParameterOfDegree p f`
* positivity of the canonical degree-`p` Lipschitz constant when the source ratio `γ_p(f)` is
  used as an honest real quotient, recorded by
  `HasPositiveIteratedFDerivLipschitzConstantOfDegree p f`

Derived API:
* the source-style whole-space norm estimate for `iteratedFDeriv ℝ (p - 1) f`
* the canonical infimum `L_p(f)` once `f` admits a finite degree-`p` derivative Lipschitz
  constant
* the canonical supremum `σ_p(f)` once the degree-`p` uniform-convexity witnesses are known to be
  nonempty and bounded above
* the quotient `γ_p(f) = σ_p(f) / L_p(f)` once `L_p(f)` is known to be strictly positive

This file therefore keeps the Chapter 4 quantities as the public source-facing owners and reduces
the whole-space derivative-Lipschitz layer to the upstream `Set.univ` owner
`f ∈ 𝒞^{p - 1,p - 1}_{L}(Set.univ)` instead of duplicating it through a real-valued wrapper
predicate. It also makes explicit the owner hypotheses needed for the real-valued source
parameters: `L_p(f)` keeps its canonical infimum definition on the finite-Lipschitz owner,
`σ_p(f)` is only formed when the source witness set is nonempty and bounded above, and `γ_p(f)`
is only formed when the canonical denominator `L_p(f)` is strictly positive. -/

section Smoothness

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function admits a finite degree-`p` Lipschitz constant when some nonnegative constant
witnesses the whole-space owner predicate from Definition 4.2.10. -/
class HasIteratedFDerivLipschitzConstantOfDegree (p : ℕ) (f : E → ℝ) : Prop where
  /-- Existence of a global degree-`p` Lipschitz constant for the `(p - 1)`st derivative of `f`.
  -/
  exists_mem : ∃ L : NNReal, f ∈ 𝒞^{p - 1,p - 1}_{L}(Set.univ)

namespace HasIteratedFDerivLipschitzConstantOfDegree

/-- A concrete degree-`p` Lipschitz constant yields the finiteness owner. -/
theorem of_constant
    {L : NNReal} {p : ℕ} {f : E → ℝ}
    (hL : f ∈ 𝒞^{p - 1,p - 1}_{L}(Set.univ)) :
    HasIteratedFDerivLipschitzConstantOfDegree p f :=
  ⟨⟨L, hL⟩⟩

/-- An existential degree-`p` Lipschitz witness yields the finiteness owner. -/
theorem of_exists
    {p : ℕ} {f : E → ℝ}
    (h : ∃ L : NNReal, f ∈ 𝒞^{p - 1,p - 1}_{L}(Set.univ)) :
    HasIteratedFDerivLipschitzConstantOfDegree p f :=
  ⟨h⟩

/-- Finite degree-`p` Lipschitz control of the `(p - 1)`st derivative implies
`C^(p - 1)` regularity. -/
theorem contDiff
    {p : ℕ} {f : E → ℝ}
    [hf : HasIteratedFDerivLipschitzConstantOfDegree p f] :
    ContDiff ℝ (p - 1 : ℕ) f := by
  rcases hf.exists_mem with ⟨L, hL⟩
  exact contDiffOn_univ.mp <| taylorCoeffLipschitzClass.contDiffOn hL

/-- The upstream owner recovers the source-style global norm estimate for the `(p - 1)`st
iterated derivative. -/
theorem norm_sub_le
    {L : NNReal} {p : ℕ} {f : E → ℝ}
    (hL : f ∈ 𝒞^{p - 1,p - 1}_{L}(Set.univ))
    (x y : E) :
    ‖iteratedFDeriv ℝ (p - 1) f x - iteratedFDeriv ℝ (p - 1) f y‖ ≤ (L : ℝ) * ‖x - y‖ := by
  simpa [iteratedFDerivWithin_univ] using
    taylorCoeffLipschitzClass.norm_sub_le_iteratedFDerivWithin hL
      (uniqueDiffOn_univ : UniqueDiffOn ℝ (Set.univ : Set E)) (by simp) (by simp)

end HasIteratedFDerivLipschitzConstantOfDegree

/-- The canonical degree-`p` Lipschitz constant `L_p(f)`, defined as the infimum of all global
Lipschitz constants for the `(p - 1)`st derivative of `f` once `f` admits such a constant. -/
def iteratedFDerivLipschitzConstantOfDegree
    (f : E → ℝ) (p : ℕ) [HasIteratedFDerivLipschitzConstantOfDegree p f] : NNReal :=
  sInf {L : NNReal | f ∈ 𝒞^{p - 1,p - 1}_{L}(Set.univ)}

/-- The canonical degree-`p` Lipschitz constant is strictly positive. This owner is the domain on
which the source ratio `γ_p(f)` is a genuine real quotient rather than a totalized zero-division
artifact. -/
class HasPositiveIteratedFDerivLipschitzConstantOfDegree
    (p : ℕ) (f : E → ℝ) [HasIteratedFDerivLipschitzConstantOfDegree p f] : Prop where
  /-- Positivity of the canonical infimum `L_p(f)`. -/
  pos : 0 < (iteratedFDerivLipschitzConstantOfDegree f p : ℝ)

namespace HasPositiveIteratedFDerivLipschitzConstantOfDegree

theorem lipschitzConstant_pos
    {p : ℕ} {f : E → ℝ}
    [HasIteratedFDerivLipschitzConstantOfDegree p f]
    [hf : HasPositiveIteratedFDerivLipschitzConstantOfDegree p f] :
    0 < (iteratedFDerivLipschitzConstantOfDegree f p : ℝ) :=
  hf.pos

end HasPositiveIteratedFDerivLipschitzConstantOfDegree

end Smoothness

section Conditioning

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function admits a finite degree-`p` uniform-convexity parameter when the positive whole-space
degree-`p` uniform-convexity witnesses form a nonempty set that is bounded above in `ℝ`. This is
exactly the domain on which the source supremum `σ_p(f)` is a genuine real parameter. -/
class HasUniformConvexityParameterOfDegree (p : ℕ) (f : E → ℝ) : Prop where
  /-- Existence of a positive whole-space degree-`p` uniform-convexity witness. -/
  exists_mem : ∃ σ > 0,
    UniformConvexOn Set.univ (uniformConvexPowerModulus σ (p : ℝ)) f
  /-- The positive witness set defining `σ_p(f)` is bounded above in `ℝ`. -/
  bddAbove : BddAbove
    {σ : ℝ | 0 < σ ∧ UniformConvexOn Set.univ (uniformConvexPowerModulus σ (p : ℝ)) f}

namespace HasUniformConvexityParameterOfDegree

theorem nonempty
    {p : ℕ} {f : E → ℝ}
    [hf : HasUniformConvexityParameterOfDegree p f] :
    Set.Nonempty
      {σ : ℝ | 0 < σ ∧ UniformConvexOn Set.univ (uniformConvexPowerModulus σ (p : ℝ)) f} := by
  rcases hf.exists_mem with ⟨σ, hσ, huniform⟩
  exact ⟨σ, hσ, huniform⟩

end HasUniformConvexityParameterOfDegree

/-- The canonical degree-`p` uniform-convexity parameter `σ_p(f)`, defined as the supremum of all
positive constants whose degree-`p` power modulus witnesses the canonical owner predicate
`UniformConvexOn Set.univ`. This source quantity is formed only on the owner
`HasUniformConvexityParameterOfDegree p f`, which records that the defining witness set is
nonempty and bounded above. -/
def uniformConvexityParameterOfDegree
    (f : E → ℝ) (p : ℕ) [HasUniformConvexityParameterOfDegree p f] : ℝ :=
  sSup
    {σ : ℝ |
      0 < σ ∧ UniformConvexOn Set.univ (uniformConvexPowerModulus σ (p : ℝ)) f}

namespace HasUniformConvexityParameterOfDegree

theorem le_uniformConvexityParameterOfDegree
    {p : ℕ} {f : E → ℝ} [hf : HasUniformConvexityParameterOfDegree p f]
    {σ : ℝ}
    (hσ : 0 < σ)
    (huniform : UniformConvexOn Set.univ (uniformConvexPowerModulus σ (p : ℝ)) f) :
    σ ≤ uniformConvexityParameterOfDegree f p :=
  le_csSup hf.bddAbove ⟨hσ, huniform⟩

theorem uniformConvexityParameterOfDegree_pos
    {p : ℕ} {f : E → ℝ} [hf : HasUniformConvexityParameterOfDegree p f] :
    0 < uniformConvexityParameterOfDegree f p := by
  rcases hf.exists_mem with ⟨σ, hσ, huniform⟩
  exact lt_of_lt_of_le hσ <| le_uniformConvexityParameterOfDegree hσ huniform

end HasUniformConvexityParameterOfDegree

/-- Definition 4.2.11: for a function `f` and degree `p`, the degree-`p` condition number
`γ_p(f)` is the ratio `σ_p(f) / L_p(f)` of its degree-`p` uniform-convexity parameter and its
degree-`p` Lipschitz constant for the `(p - 1)`st derivative. This is defined only when `σ_p(f)`
is a genuine real parameter and the canonical denominator `L_p(f)` is strictly positive. -/
def conditionNumberOfDegree
    (f : E → ℝ) (p : ℕ)
    [HasUniformConvexityParameterOfDegree p f]
    [HasIteratedFDerivLipschitzConstantOfDegree p f]
    [HasPositiveIteratedFDerivLipschitzConstantOfDegree p f] : ℝ :=
  uniformConvexityParameterOfDegree f p / iteratedFDerivLipschitzConstantOfDegree f p

end Conditioning

namespace DegreeConditioning

scoped notation:max "L[" p "](" f ")" => iteratedFDerivLipschitzConstantOfDegree f p
scoped notation:max "σ[" p "](" f ")" => uniformConvexityParameterOfDegree f p
scoped notation:max "γ[" p "](" f ")" => conditionNumberOfDegree f p

end DegreeConditioning

open scoped DegreeConditioning

/-- Expanding `γ[p](f)` recovers the quotient `σ[p](f) / L[p](f)`. -/
theorem conditionNumberOfDegree_eq_ratio
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (p : ℕ)
    [HasUniformConvexityParameterOfDegree p f]
    [HasIteratedFDerivLipschitzConstantOfDegree p f]
    [HasPositiveIteratedFDerivLipschitzConstantOfDegree p f] :
    γ[p](f) = σ[p](f) / L[p](f) :=
  rfl
