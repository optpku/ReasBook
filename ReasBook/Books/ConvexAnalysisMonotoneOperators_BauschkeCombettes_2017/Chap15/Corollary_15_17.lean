/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_6
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Corollary_15_16

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

section FenchelDuality

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Corollary 15.17 is the translated-quadratic minorant conclusion
  `q (x - w) ≤ f(x) + q(x)`.
- `core/canonical`: the owner abstraction is
  `exists_dual_vector_with_explicit_bounds_of_primalObjective_nonneg_and_conjugate_eq_reflection`
  from Corollary 15.16, specialized to the quadratic owner `halfSquaredNorm`.
- `bridge/view`: Example 13.6 supplies the reflected-conjugate identity for
  `halfSquaredNorm.asEReal`, while `halfSquaredNorm ∈ Γ₀(H)` and
  `effectiveDomain halfSquaredNorm = univ` are derived support facts, not new
  source-facing owners.
-/

-- Proof sketch: apply Corollary 15.16 with `g = halfSquaredNorm`. Example 13.6
-- gives the reflected-conjugate identity for this quadratic kernel, and its effective domain is
-- all of `H`, so the strong-relative-interior side condition reduces to the regularity built into
-- the quadratic perturbation. If Corollary 15.16 yields `v`, then rewrite its conclusion as
-- `q (x - (-v)) ≤ f x + q x` and take `w = -v`.
/-- Corollary 15.17: if `f ∈ Γ₀(H)` and `f + (1/2)‖·‖²` is pointwise nonnegative, then some
translate of the quadratic function is pointwise dominated by `f + (1/2)‖·‖²`. -/
theorem exists_halfSquaredNorm_sub_le_pointwiseAdd
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (h_nonneg : ∀ x : H,
      (0 : EReal) ≤
        (f x : EReal) + (halfSquaredNorm x : EReal)) :
    ∃ w : H, ∀ x : H,
      (halfSquaredNorm (x - w) : EReal) ≤ (f x : EReal) + (halfSquaredNorm x : EReal) := by
  have halfSquaredNorm_eq_toEReal :
      ((fun x : H ↦ ((‖x‖ ^ 2) / 2 : ℝ)).toEReal) =
        (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) := by
    funext x
    simp [halfSquaredNorm, moreauQuadraticKernel, div_eq_mul_inv, mul_comm]
  have hhalf : halfSquaredNorm ∈ Γ₀(H) := by
    rw [← halfSquaredNorm_eq_toEReal]
    refine toEReal_mem_gammaZero_of_mem_gamma ?_
    rw [mem_gamma_iff]
    refine ⟨?_, ?_⟩
    · intro x y a ha0 ha1
      have hnorm_sq :
          _root_.ConvexOn ℝ (Set.univ : Set H) (fun x : H ↦ ‖x‖ ^ 2) :=
        (convexOn_univ_norm : _root_.ConvexOn ℝ (Set.univ : Set H) (fun x : H ↦ ‖x‖)).pow
          (fun x _ ↦ norm_nonneg x) 2
      have hconv :
          ‖a • x + (1 - a) • y‖ ^ 2 / 2 ≤
            a * (‖x‖ ^ 2 / 2) + (1 - a) * (‖y‖ ^ 2 / 2) := by
        have hnorm_sq' :
            ‖a • x + (1 - a) • y‖ ^ 2 ≤ a * ‖x‖ ^ 2 + (1 - a) * ‖y‖ ^ 2 := by
          simpa [smul_eq_mul] using
            hnorm_sq.2 (by simp) (by simp) ha0 (sub_nonneg.mpr ha1) (by ring)
        nlinarith
      change (((‖a • x + (1 - a) • y‖ ^ 2) / 2 : ℝ) : EReal) ≤
          (((a * (‖x‖ ^ 2 / 2) + (1 - a) * (‖y‖ ^ 2 / 2) : ℝ)) : EReal)
      exact_mod_cast hconv
    · have hcont : Continuous fun x : H ↦ ((‖x‖ ^ 2) / 2 : ℝ) := by
        simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          (continuous_norm.pow 2).const_mul (1 / 2 : ℝ)
      have hcontE : Continuous fun x : H ↦ ((((‖x‖ ^ 2) / 2 : ℝ) : EReal)) := by
        simpa using continuous_coe_real_ereal.comp hcont
      simpa using hcontE.lowerSemicontinuous
  have hdom : effectiveDomain halfSquaredNorm = (Set.univ : Set H) := by
    rw [← halfSquaredNorm_eq_toEReal]
    exact Function.effectiveDomain_toEReal (fun x : H ↦ ((‖x‖ ^ 2) / 2 : ℝ))
  have hsri :
      (0 : H) ∈ sri (effectiveDomain f - effectiveDomain halfSquaredNorm) := by
    rw [hdom]
    obtain ⟨x, hx⟩ : (effectiveDomain f).Nonempty := ConvexOn.nonempty hf.2
    have hsub : effectiveDomain f - (Set.univ : Set H) = Set.univ := by
      ext y
      constructor
      · intro hy
        simp
      · intro hy
        exact Set.mem_sub.mpr ⟨x, hx, x - y, by simp, by abel⟩
    rw [hsub]
    rw [Set.mem_strongRelativeInterior_iff]
    refine ⟨by simp, ?_⟩
    ext y
    constructor
    · intro hy
      simp
    · intro hy
      rw [Set.cone_def]
      exact ConvexCone.subset_hull (by simp)
  have hreflect :
      ((halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal)∗ =
        ((halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal)ᵛ := by
    calc
      ((halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal)∗ =
          ((halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal) := fenchelConjugate_halfSquaredNorm
      _ = ((halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal)ᵛ := by
          ext x
          simp [norm_neg]
  obtain ⟨v, hv⟩ :=
    exists_dual_vector_with_explicit_bounds_of_primalObjective_nonneg_and_conjugate_eq_reflection
      f halfSquaredNorm hf hhalf hsri hreflect (fun x ↦ by simpa [primalObjective] using h_nonneg x)
  refine ⟨-v, ?_⟩
  intro x
  rcases hv x with ⟨hleft, _⟩
  have hquad :
      (halfSquaredNorm (x + v) : EReal) =
        (halfSquaredNorm x : EReal) + (((⟪x, v⟫_ℝ : ℝ) : EReal) + (halfSquaredNorm v : EReal)) := by
    have hreal :
        (‖x + v‖ ^ 2) / 2 = (‖x‖ ^ 2) / 2 + (⟪x, v⟫_ℝ + (‖v‖ ^ 2) / 2) := by
      rw [norm_add_sq_real]
      ring
    rw [halfSquaredNorm_apply, halfSquaredNorm_apply, halfSquaredNorm_apply]
    exact_mod_cast hreal
  rw [sub_eq_add_neg, neg_neg, hquad]
  exact hleft

end FenchelDuality

end ERealFunction
