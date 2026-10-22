/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Definition_10_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Proposition_10_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

-- Proof sketch: the forward implication is `UniformlyConvex.modulus_eq_zero_iff` specialized to
-- the exact modulus. For the reverse implication, use Proposition 10.12 to obtain monotonicity
-- and the value at `0`, then verify the defining Jensen inequality for
-- `UniformlyConvex f (exactModulusOfConvexity f)` from the infimum property of
-- `exactModulusOfConvexity`.
/-- Corollary 10.13, canonical owner form: the exact modulus of convexity is itself a modulus of
uniform convexity precisely when it vanishes only at `0`. -/
theorem exactModulusOfConvexity_uniformlyConvex_iff
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) :
    UniformlyConvex f (exactModulusOfConvexity f) ↔
      ∀ r : NNReal, exactModulusOfConvexity f r = 0 ↔ r = 0 := sorry

/-- If `f` is uniformly convex with some modulus, then its exact modulus of convexity vanishes only
at `0`. -/
theorem UniformlyConvex.exactModulusOfConvexity_eq_zero_iff
    {f : H → Set.Ioi (⊥ : EReal)} {ψ : NNReal → EReal} (hf : UniformlyConvex f ψ)
    (r : NNReal) :
    exactModulusOfConvexity f r = 0 ↔ r = 0 := sorry

/-- A strongly convex function is uniformly convex with its exact modulus of convexity. -/
theorem StronglyConvex.uniformlyConvex_exactModulusOfConvexity
    {f : H → Set.Ioi (⊥ : EReal)} {β : ℝ} (hf : StronglyConvex f β) :
    UniformlyConvex f (exactModulusOfConvexity f) := by
  refine (exactModulusOfConvexity_uniformlyConvex_iff f hf.uniformlyConvex.convexOn).2 ?_
  intro r
  exact hf.uniformlyConvex.exactModulusOfConvexity_eq_zero_iff r

-- Proof sketch: the forward implication specializes the owner-style exact-modulus theorem to the
-- chosen modulus `ψ`. For the reverse implication, apply the canonical owner theorem
-- `exactModulusOfConvexity_uniformlyConvex_iff`.
/-- Corollary 10.13: a proper convex `]-∞,+∞]`-valued function is uniformly convex for some
modulus if and only if its exact modulus of convexity vanishes only at `0`. -/
theorem uniformlyConvex_exists_iff_exactModulusOfConvexity_eq_zero_iff
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) :
    (∃ ψ : NNReal → EReal, UniformlyConvex f ψ) ↔
      ∀ r : NNReal, exactModulusOfConvexity f r = 0 ↔ r = 0 := by
  constructor
  · rintro ⟨ψ, hψ⟩ r
    exact hψ.exactModulusOfConvexity_eq_zero_iff r
  · intro hzero
    exact ⟨_, (exactModulusOfConvexity_uniformlyConvex_iff f hconv).2 hzero⟩

end ERealFunction
