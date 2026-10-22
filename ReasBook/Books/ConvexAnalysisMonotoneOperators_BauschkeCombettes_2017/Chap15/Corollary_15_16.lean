/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_15
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Corollary_15_15

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

section FenchelDuality

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Corollary 15.16 is the explicit two-sided affine bound
  `f(x) + g(x) ≥ g(x) + ⟪x, v⟫ + g(v) ≥ 0`.
- `core/canonical`: the owner declarations are `primalObjective`,
  `exists_dual_vector_le_zero_of_pointwiseAdd_nonneg_and_conjugate_eq_comp`,
  and `fenchel_young_inequality`.
- `bridge/view`: the reflected-conjugate hypothesis `g.asEReal∗ = g.asERealᵛ`
  identifies Corollary 15.15 with the source-facing dual inequality
  `f.asEReal∗ v + (g v : EReal) ≤ 0`.
-/

section ExplicitInequalities

-- Proof sketch: if `f` is improper, then `f(x) = +∞` and the inequality is immediate. Otherwise
-- Fenchel--Young for `f` at `(x, v)` gives `⟪x, v⟫ ≤ f(x) + f^*(v)`. The dual-vector inequality
-- `f^*(v) + g(v) ≤ 0` rewrites to `g(v) ≤ -f^*(v)`, yielding
-- `g(x) + ⟪x, v⟫ + g(v) ≤ f(x) + g(x)`.
/-- A dual vector with `f^*(v) + g(v) ≤ 0` gives the first inequality in the explicit form of
Corollary 15.16. -/
theorem affine_shift_le_primalObjective_of_conjugate_add_value_le_zero
    (f g : H → Set.Ioi (⊥ : EReal)) (v : H)
    (hv : f.asEReal∗ v + (g v : EReal) ≤ 0)
    (x : H) :
    (g x : EReal) + (((⟪x, v⟫_ℝ : ℝ) : EReal) + (g v : EReal)) ≤
      primalObjective f g x := sorry

-- Proof sketch: the reflection identity rules out the improper case `g ≡ +∞`, so `g.asEReal` is
-- proper. Apply Fenchel--Young to `g` at `(x, -v)` and use the reflection identity
-- `g^*(-v) = g(v)` to rewrite the conjugate term.
-- Rearranging gives
-- `0 ≤ g(x) + ⟪x, v⟫ + g(v)`.
/-- The reflected-conjugate identity `g^* = gᵛ` gives the second inequality in the explicit form of
Corollary 15.16. -/
theorem zero_le_affine_shift_of_conjugate_eq_reflection
    (g : H → Set.Ioi (⊥ : EReal)) (hg_reflected : g.asEReal∗ = g.asERealᵛ)
    (x v : H) :
    (0 : EReal) ≤ (g x : EReal) + (((⟪x, v⟫_ℝ : ℝ) : EReal) + (g v : EReal)) := sorry

end ExplicitInequalities

section ExplicitCorollary

variable [CompleteSpace H]

-- Proof sketch: apply Corollary 15.15 with `L = -ContinuousLinearMap.id ℝ H`; the
-- reflected-conjugate hypothesis rewrites its conclusion to `f.asEReal∗ v + g(v) ≤ 0`. Then
-- combine the two explicit-inequality lemmas and rewrite `primalObjective f g x` as
-- `f(x) + g(x)`.
/-- Corollary 15.16: if `f, g ∈ Γ₀(H)`, if `0 ∈ sri (dom f - dom g)`, if `g^* = gᵛ`, and if
`f + g ≥ 0`, then there exists `v ∈ H` such that for every `x ∈ H`,
`f(x) + g(x) ≥ g(x) + ⟪x, v⟫ + g(v) ≥ 0`. -/
theorem
    exists_dual_vector_with_explicit_bounds_of_primalObjective_nonneg_and_conjugate_eq_reflection
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g))
    (hg_reflected : g.asEReal∗ = g.asERealᵛ)
    (hfg_nonneg : ∀ x : H, (0 : EReal) ≤ primalObjective f g x) :
    ∃ v : H, ∀ x : H,
      (g x : EReal) + (((⟪x, v⟫_ℝ : ℝ) : EReal) + (g v : EReal)) ≤
        (f x : EReal) + (g x : EReal) ∧
      (0 : EReal) ≤ (g x : EReal) + (((⟪x, v⟫_ℝ : ℝ) : EReal) + (g v : EReal)) := sorry

end ExplicitCorollary

end FenchelDuality

end ERealFunction
