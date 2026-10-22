/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped ConvexAnalysis SupportFunction

recall mem_extendedRealEffectiveDomain_iff

recall supportFunction_apply

/- Proposition 3.11 lies in the chapter's support-function / effective-domain domain.

Relevant sampled owner declarations:
- `supportFunction` / `supportFunction_apply` in `Definition_3_9`, the source-facing owner for
  `ξ[Q]`
- `extendedRealEffectiveDomain` / notation `dom` in `Definition_3_1_1_2`, the chapter owner for
  finite `EReal` values
- downstream recall `Proposition_3_1_2_3`, which already treats this file as the owner theorem
  family for bounded support-function finiteness

Best owner abstraction:
- source-facing: Proposition 3.11's bounded-set finiteness statement for `ξ[Q]`
- core/canonical: the pair `ξ[Q]` and `dom ξ[Q]`
- bridge/view: the pointwise membership theorem below, derived from the owner language rather than
  from any local wrapper

Primitive data:
- a set `Q : Set E`
- the assumptions `Q.Nonempty` and `Bornology.IsBounded Q`

Derived API:
- `supportFunction_mem_extendedRealEffectiveDomain_of_nonempty_bounded`
- `supportFunction_dom_eq_univ_of_nonempty_bounded`

No smaller upstream project or mathlib theorem with the same support-function / effective-domain
interface was found in the sampled domain, so this file remains the owner theorem family and keeps
the chapter owners `ξ[Q]` and `dom` directly on the public surface. The textbook `ℝⁿ` statement is
the specialization `E = EuclideanSpace ℝ (Fin n)`.
-/

/-- The support function of a nonempty bounded set takes finite extended-real values at every
point of a real inner-product space. The textbook `ℝⁿ` statement is the specialization
`E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: boundedness gives a uniform upper bound on the inner products `⟪u, x⟫` for
-- `x ∈ Q`, so the defining supremum is not `⊤`; nonemptiness gives one attained lower bound, so
-- the supremum is not `⊥`.
theorem supportFunction_mem_extendedRealEffectiveDomain_of_nonempty_bounded
    (Q : Set E) (hQ_nonempty : Q.Nonempty) (hQ_bounded : Bornology.IsBounded Q) (u : E) :
    u ∈ dom ξ[Q] := by
  rw [mem_extendedRealEffectiveDomain_iff, supportFunction_apply]
  constructor
  · obtain ⟨R, hR⟩ := hQ_bounded.exists_norm_le
    have hsSup_le :
        sSup ((fun x ↦ ((inner ℝ x u : ℝ) : EReal)) '' Q) ≤ ((R * ‖u‖ : ℝ) : EReal) := by
      refine sSup_le ?_
      rintro _ ⟨x, hx, rfl⟩
      change ((inner ℝ x u : ℝ) : EReal) ≤ ((R * ‖u‖ : ℝ) : EReal)
      exact_mod_cast (real_inner_le_norm x u).trans <|
        mul_le_mul_of_nonneg_right (hR x hx) (norm_nonneg u)
    exact ne_top_of_le_ne_top (EReal.coe_ne_top (R * ‖u‖)) hsSup_le
  · rcases hQ_nonempty with ⟨x, hxQ⟩
    intro hbot
    have hx_le : ((inner ℝ x u : ℝ) : EReal) ≤ sSup ((fun x ↦ ((inner ℝ x u : ℝ) : EReal)) '' Q) :=
      le_sSup ⟨x, hxQ, rfl⟩
    have : ((inner ℝ x u : ℝ) : EReal) ≤ (⊥ : EReal) := by
      rw [hbot] at hx_le
      exact hx_le
    exact (not_le_of_gt (EReal.bot_lt_coe _)) this

/-- Proposition 3.11: if `Q` is a nonempty bounded subset of a real inner-product space `E`,
then the domain `dom ξ_Q` of its support function is all of `E`; equivalently, `ξ_Q(u)` is finite
for every `u ∈ E`. The textbook `ℝⁿ` statement is the specialization
`E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: use
-- `supportFunction_mem_extendedRealEffectiveDomain_of_nonempty_bounded` pointwise to show every
-- `u` belongs to the finite-value domain of `supportFunction Q`, then conclude by extensionality
-- that this domain is `Set.univ`.
theorem supportFunction_dom_eq_univ_of_nonempty_bounded
    (Q : Set E) (hQ_nonempty : Q.Nonempty) (hQ_bounded : Bornology.IsBounded Q) :
    dom ξ[Q] = Set.univ := by
  refine Set.eq_univ_iff_forall.mpr fun u ↦ ?_
  exact supportFunction_mem_extendedRealEffectiveDomain_of_nonempty_bounded
    Q hQ_nonempty hQ_bounded u

end
