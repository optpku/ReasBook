/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Proposition_15_5
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Theorem_15_3

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

universe u

namespace ERealFunction

set_option linter.style.longLine false

section AttouchBrezisTheorem

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private theorem
    zero_mem_strongRelativeInterior_sub_effectiveDomain_of_zero_mem_core_sub_effectiveDomain
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hcore : (0 : H) ∈ core (effectiveDomain f - effectiveDomain g)) :
    (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g) := by
  apply zero_mem_strongRelativeInterior_sub_effectiveDomain_of_mem_gammaZero_of_regularity hf hg
  change
    cone (effectiveDomain f - effectiveDomain g) =
        (((Submodule.span ℝ (effectiveDomain f - effectiveDomain g)).topologicalClosure :
          Submodule ℝ H) : Set H) ∨
      (0 : H) ∈ core (effectiveDomain f - effectiveDomain g) ∨
      (0 : H) ∈ interior (effectiveDomain f - effectiveDomain g) ∨
      (∃ x ∈ effectiveDomain g, ∃ ρ : ℝ, 0 < ρ ∧
        Metric.ball x ρ ⊆ effectiveDomain f ∧
        ContinuousAt (fun y : H ↦ (f y : EReal).toReal) x) ∨
      (FiniteDimensional ℝ H ∧
        (ri (effectiveDomain f) ∩ ri (effectiveDomain g)).Nonempty)
  exact Or.inr <| Or.inl hcore

-- Proof sketch: the Attouch--Brezis core hypothesis is the regularity condition ensuring that the
-- dual regularity predicate of Proposition 15.5, hence yields
-- `0 ∈ sri (effectiveDomain f - effectiveDomain g)`. Theorem 15.3 then supplies the exact
-- Attouch--Brézis conjugacy identity and exactness result on the dual side.
/-- Proposition 15.2: if `f` and `g` belong to `Γ₀(H)` and `0 ∈ core (dom f - dom g)`, then the
Fenchel conjugate of the pointwise sum `f + g` is `f^* □ g^*`, and the companion theorem shows
that this infimal convolution is exact. -/
theorem
    conjugate_pointwiseAdd_eq_infimalConvolution_conjugates_of_zero_mem_core_sub_effectiveDomain
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hcore : (0 : H) ∈ core (effectiveDomain f - effectiveDomain g)) :
    (f + g).asEReal∗ = f.asEReal∗ □ g.asEReal∗ := by
  have hsri :
      (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g) :=
    zero_mem_strongRelativeInterior_sub_effectiveDomain_of_zero_mem_core_sub_effectiveDomain
      f g hf hg hcore
  exact
    conjugate_pointwiseAdd_eq_infimalConvolution_conjugates_of_zero_mem_sri_sub_effectiveDomain
      f g hf hg hsri

-- Proof sketch: the core hypothesis is the corresponding regularity branch of Proposition 15.5,
-- so it yields `0 ∈ sri (effectiveDomain f - effectiveDomain g)`. Then invoke the exactness
-- component of Theorem 15.3.
/-- Under the Attouch--Brezis core regularity hypothesis, the infimal convolution of the packaged
Fenchel conjugates is exact. -/
theorem infimalConvolution_exact_gammaZeroConjugates_of_zero_mem_core_sub_effectiveDomain
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hcore : (0 : H) ∈ core (effectiveDomain f - effectiveDomain g)) :
    infimalConvolution.Exact (gammaZeroConjugate f hf) (gammaZeroConjugate g hg) := by
  have hsri :
      (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g) :=
    zero_mem_strongRelativeInterior_sub_effectiveDomain_of_zero_mem_core_sub_effectiveDomain
      f g hf hg hcore
  exact
    infimalConvolution_exact_gammaZeroConjugates_of_zero_mem_sri_sub_effectiveDomain
      f g hf hg hsri

end AttouchBrezisTheorem

end ERealFunction
