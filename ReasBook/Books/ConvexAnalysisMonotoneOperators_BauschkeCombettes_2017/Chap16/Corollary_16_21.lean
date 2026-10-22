/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap14.Proposition_14_15
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap14.Theorem_14_17
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section BoundednessAndConjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

-- Proof sketch: Proposition 14.15 gives `(i) → (iii)`. Theorem 14.17 identifies clause `(ii)` with
-- `interior (dom f*) = Set.univ`, which is equivalent to `dom f* = Set.univ`. For `(iii) → (i)`,
-- Corollary 13.38 shows that `f* ∈ Γ₀(H)`; since `dom f* = Set.univ`, the conjugate is finite
-- everywhere, and Corollary 8.40 makes this finite-dimensional convex function continuous.
-- Proposition 16.20 then yields supercoercivity of `(f*)*`, which Corollary 13.38 identifies with
-- `f`.
/-- Corollary 16.21: for `f ∈ Γ₀(H)` on a finite-dimensional real Hilbert space, the following are
equivalent: `f` is supercoercive, every linear perturbation `f - ⟪·, u⟫` is coercive, and the
effective domain of the Fenchel conjugate `f*` is all of `H`. -/
theorem supercoercive_tfae_coercive_sub_inner_dom_conjugate_univ_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    List.TFAE
      [Supercoercive f.asEReal,
        ∀ u : H,
          Coercive (f.asEReal - fun x ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal)),
        dom f.asEReal∗ = Set.univ] := by
  have hfStar : f∗[hf] ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hf
  tfae_have 1 ↔ 3 := by
    constructor
    · intro hsuper
      exact dom_conjugate_eq_univ_of_conjugate_boundedOnEveryBoundedSet f
        ((supercoercive_iff_conjugate_boundedOnEveryBoundedSet f hf).mp hsuper)
    · intro hdom
      have hdom_fStar : effectiveDomain (f∗[hf]) = Set.univ := by
        ext u
        rw [mem_effectiveDomain_iff]
        have hu_dom : u ∈ dom f.asEReal∗ := by simp [hdom]
        simpa [gammaZeroConjugate_apply] using (mem_dom_iff _ _).1 hu_dom
      have hconv_fStar :
          _root_.ConvexOn ℝ Set.univ (fun u ↦ (f∗[hf] u : EReal).toReal) := by
        simpa [hdom_fStar] using hfStar.2.toReal_convexOn_effectiveDomain
      have hbounded_fStar :
          ∀ B : Set H, Bornology.IsBounded B →
            ∃ M : ℝ, ∀ u ∈ B, (f∗[hf] u : EReal) ≤ M := by
        intro B hB
        have himage :
            Bornology.IsBounded ((fun u ↦ (f∗[hf] u : EReal).toReal) '' B) :=
          boundedOnEveryBoundedSet_of_convex_finiteDimensional
            (fun u ↦ (f∗[hf] u : EReal).toReal) hconv_fStar B hB
        rcases himage.subset_ball (0 : ℝ) with ⟨R, hR⟩
        refine ⟨R, ?_⟩
        intro u hu
        have hu_ball :
            (f∗[hf] u : EReal).toReal ∈ Metric.ball (0 : ℝ) R :=
          hR ⟨u, hu, rfl⟩
        have hu_lt : (f∗[hf] u : EReal).toReal < R := by
          have hu_abs : -R < (f∗[hf] u : EReal).toReal ∧ (f∗[hf] u : EReal).toReal < R := by
            simpa [Metric.mem_ball, Real.dist_eq, abs_lt] using hu_ball
          exact hu_abs.2
        have hu_top : (f∗[hf] u : EReal) ≠ ⊤ := by
          have hu_eff : u ∈ effectiveDomain (f∗[hf]) := by simp [hdom_fStar]
          exact ne_of_lt ((mem_effectiveDomain_iff).1 hu_eff)
        have hu_bot : (f∗[hf] u : EReal) ≠ ⊥ := by
          exact ne_of_gt (f∗[hf] u).2
        have hu_eReal : (((f∗[hf] u : EReal).toReal : ℝ) : EReal) < (R : EReal) := by
          exact_mod_cast hu_lt
        calc
          (f∗[hf] u : EReal) = (((f∗[hf] u : EReal).toReal : ℝ) : EReal) := by
            symm
            exact EReal.coe_toReal hu_top hu_bot
          _ ≤ (R : EReal) := le_of_lt hu_eReal
      exact
        (supercoercive_iff_conjugate_boundedOnEveryBoundedSet f hf).2 <| by
          intro B hB
          rcases hbounded_fStar B hB with ⟨M, hM⟩
          refine ⟨M, ?_⟩
          intro u hu
          simpa [gammaZeroConjugate_apply] using hM u hu
  tfae_have 2 ↔ 3 := by
    constructor
    · intro hcoercive
      ext u
      constructor
      · intro _
        simp
      · intro _
        exact interior_subset <|
          (coercive_sub_inner_iff_mem_interior_dom_conjugate f hf u).1 (hcoercive u)
    · intro hdom u
      rw [coercive_sub_inner_iff_mem_interior_dom_conjugate f hf]
      simp [hdom]
  tfae_finish

end BoundednessAndConjugation

end ERealFunction
