/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace ERealFunction

variable (𝕜 : Type u) [Semiring 𝕜] [PartialOrder 𝕜]
variable {H : Type v} [AddCommMonoid H] [SMul 𝕜 H]

variable (f : H → EReal)

/- Definition 10.20: the textbook notion of a quasiconvex `]-∞,+∞]`-valued function is the
canonical mathlib predicate `QuasiconvexOn 𝕜 Set.univ f`; the textbook real-vector-space version
is the specialization `𝕜 = ℝ`. -/
#check QuasiconvexOn 𝕜 Set.univ f

/-- Global quasiconvexity of an extended-real-valued function is equivalent to convexity of each
real lower level set. -/
-- Proof sketch: the forward direction is the defining owner predicate at real thresholds. For the
-- reverse direction, use the owner constructor `Convex.quasiconvexOn_of_convex_le` on `univ`; the
-- only extra work is to handle the `⊥` threshold as the intersection of all real lower level
-- sets, while the `⊤` threshold is `univ`.
theorem quasiconvexOn_univ_iff_convex_lowerLevelSet :
    QuasiconvexOn 𝕜 Set.univ f ↔ ∀ ξ : ℝ, Convex 𝕜 (lowerLevelSet f ξ) := by
  constructor
  · intro hf ξ
    simpa [QuasiconvexOn, lowerLevelSet] using hf (ξ : EReal)
  · intro h
    refine (convex_univ : Convex 𝕜 (Set.univ : Set H)).quasiconvexOn_of_convex_le ?_
    rw [EReal.forall]
    refine ⟨?_, ?_, ?_⟩
    · have hbot_eq : {x | f x = (⊥ : EReal)} = ⋂ ξ : ℝ, lowerLevelSet f ξ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_iInter, mem_lowerLevelSet_iff]
        constructor
        · intro hx ξ
          simp [hx]
        · intro hx
          by_contra hxbot
          have hbot_lt : (⊥ : EReal) < f x := bot_lt_iff_ne_bot.mpr hxbot
          rcases EReal.lt_iff_exists_real_btwn.mp hbot_lt with ⟨ξ, -, hξ⟩
          exact (not_le.mpr hξ) (hx ξ)
      simpa [hbot_eq] using convex_iInter h
    · simpa using (convex_univ : Convex 𝕜 (Set.univ : Set H))
    · intro ξ
      simpa [lowerLevelSet] using h ξ

end ERealFunction
