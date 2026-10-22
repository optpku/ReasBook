/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Corollary_12_31
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_15
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Proposition_15_13

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

section FenchelDuality

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-
Source/core/bridge triage:
- `source-facing`: Corollary 15.14 states the cone-constrained minimization formula
  `inf_{x ∈ K} f(x) = - min_{u ∈ Kᵒ⊕} f^*(u)`.
- `core/canonical`: the owner declarations are `primalOptimalValue`, `fenchelDualObjective`, and
  Proposition 15.13.
- `bridge/view`: the constrained problem is encoded by the canonical indicator `ι[K]`; Example
  13.3 identifies its conjugate, and Definition 6.22 transports minimizers from the polar cone to
  the dual cone by negation.
-/

-- Proof-engineering fact: the strong-relative-interior hypothesis already forces the constraint
-- set to be nonempty, because membership in `sri (effectiveDomain f - K)` implies membership in
-- `effectiveDomain f - K`.
omit [CompleteSpace H] in
private theorem nonempty_of_zero_mem_sri_sub_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (K : Set H)
    (hsri : (0 : H) ∈ sri (effectiveDomain f - K)) :
    K.Nonempty := by
  rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hzero, _⟩
  rcases Set.mem_sub.mp hzero with ⟨_, _, y, hy, _⟩
  exact ⟨y, hy⟩

omit [CompleteSpace H] in
private theorem zero_mem_polarCone (K : Set H) :
    (0 : H) ∈ Kᵒ⊖ := by
  rw [Set.mem_polarCone_iff_forall_inner_nonpos]
  intro x hx
  simp

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
private theorem primalOptimalValue_indicator_eq_sInf_image
    (f : H → Set.Ioi (⊥ : EReal)) (K : Set H) :
    primalOptimalValue f (ι[K]) = sInf (f.asEReal '' K) := by
  rw [primalOptimalValue_def]
  apply le_antisymm
  · exact (isGLB_sInf (f.asEReal '' K)).2 <| by
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact (isGLB_sInf (Set.range (primalObjective f (ι[K])))).1 <| by
        refine ⟨x, ?_⟩
        simp [primalObjective, ERealFunction.indicator, hx]
  · exact (isGLB_sInf (Set.range (primalObjective f (ι[K])))).2 <| by
      rintro y ⟨x, rfl⟩
      by_cases hx : x ∈ K
      · simpa [primalObjective, ERealFunction.indicator, hx] using
          (isGLB_sInf (f.asEReal '' K)).1 (Set.mem_image_of_mem _ hx)
      · have hx_add_top : (f x : EReal) + ⊤ = ⊤ :=
          EReal.add_top_of_ne_bot (ne_of_gt (f x).2)
        simp [primalObjective, ERealFunction.indicator, hx, hx_add_top]

omit [CompleteSpace H] in
private theorem fenchelDualObjective_indicator_eq_conjugate_neg_of_mem_polar
    (f : H → Set.Ioi (⊥ : EReal)) (K : Set H) {u : H}
    (hindicator_conj : ((ι[K]).asEReal)∗ = (ι[Kᵒ⊖]).asEReal)
    (hu : u ∈ Kᵒ⊖) :
    fenchelDualObjective f (ι[K]) u = f.asEReal∗ (-u) := by
  rw [fenchelDualObjective_apply, hindicator_conj]
  simp [ERealFunction.indicator, hu]

omit [CompleteSpace H] in
private theorem neg_mem_argminOn_conjugate_of_mem_argminOn_reflectedConjugate
    (f : H → Set.Ioi (⊥ : EReal)) (K : Set H) {v : H}
    (hv : v ∈ Argmin[Kᵒ⊖] f.asEReal∗ᵛ) :
    -v ∈ Argmin[Kᵒ⊕] f.asEReal∗ := by
  rcases mem_argminOn_iff.mp hv with ⟨hvK, hvmin⟩
  refine mem_argminOn_iff.mpr ?_
  constructor
  · rw [Set.mem_dualCone_iff]
    simpa using hvK
  · rw [isMinOn_iff] at hvmin ⊢
    intro u hu
    simpa using hvmin (-u) <| Set.mem_dualCone_iff.mp hu

-- Proof sketch: apply Proposition 15.13 with `g = ι_K`, where closed convexity places the
-- indicator of `K` in `Γ₀(H)`. The strong-relative-interior hypothesis is exactly the required
-- regularity condition. Then use Example 13.3(ii) together with Definition 6.22 to rewrite the
-- conjugate of `ι_K` as the indicator of the dual cone `Kᵒ⊕`, so minimizing the Chapter 15 dual
-- objective becomes minimizing `f*` over `Kᵒ⊕`.
/-- Corollary 15.14: if `f ∈ Γ₀(H)` and `K` is a closed convex cone with
`0 ∈ sri (effectiveDomain f - K)`, then the infimum of `f` over `K` is the negative of the
minimum of the Fenchel conjugate over the dual cone `Kᵒ⊕`. -/
theorem exists_mem_argminOn_conjugate_dualCone_eq_neg_sInf_image_of_zero_mem_sri_sub_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (K : Set H) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K) (hK_cone : IsCone K)
    (hsri : (0 : H) ∈ sri (effectiveDomain f - K)) :
    ∃ u ∈ Argmin[Kᵒ⊕] f.asEReal∗,
      sInf (f.asEReal '' K) = -f.asEReal∗ u := by
  let h : H → EReal := fenchelDualObjective f (ι[K])
  have hK_nonempty : K.Nonempty :=
    nonempty_of_zero_mem_sri_sub_effectiveDomain f K hsri
  have hindicator_gamma : ι[K] ∈ Γ₀(H) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex hK_nonempty hK_closed hK_convex
  have hindicator_conj : ((ι[K]).asEReal)∗ = (ι[Kᵒ⊖]).asEReal :=
    conjugate_indicator_eq_indicator_polarCone_of_nonempty_isCone K hK_nonempty hK_cone
  have hsri_indicator : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain (ι[K])) := by
    simpa using hsri
  obtain ⟨v, hvArg, hvEq⟩ :=
    exists_mem_argmin_fenchelDualObjective_eq_neg_primalOptimalValue_of_zero_mem_sri_sub_effectiveDomain
      f
      (ι[K])
      hf
      hindicator_gamma
      hsri_indicator
  have hf_proper : IsProper f.asEReal :=
    isProper_of_mem_gammaZero hf
  have hvmin : IsMinOn h Set.univ v := by
    simpa [h] using (mem_argmin_iff.mp hvArg)
  have hzero_polar : (0 : H) ∈ Kᵒ⊖ :=
    zero_mem_polarCone K
  obtain ⟨w, hw_polar, hw_arg⟩ : ∃ w ∈ Kᵒ⊖, w ∈ Argmin h := by
    by_cases hv_polar : v ∈ Kᵒ⊖
    · exact ⟨v, hv_polar, by simpa [h] using hvArg⟩
    · refine ⟨0, hzero_polar, ?_⟩
      rw [mem_argmin_iff, isMinOn_univ_iff]
      intro y
      have hv_conj_ne_bot : f.asEReal∗ (-v) ≠ ⊥ :=
        conjugate_ne_bot_of_isProper hf_proper (-v)
      have hv_top : h v = ⊤ := by
        rw [show h v = fenchelDualObjective f (ι[K]) v by rfl, fenchelDualObjective_apply,
          hindicator_conj]
        change f.asEReal∗ (-v) + (ι[Kᵒ⊖] v : EReal) = ⊤
        have hv_indicator : (ι[Kᵒ⊖] v : EReal) = ⊤ := by
          simp [ERealFunction.indicator, hv_polar]
        rw [hv_indicator]
        exact EReal.add_top_of_ne_bot hv_conj_ne_bot
      have hy_top : h y = ⊤ := by
        have hvy : h v ≤ h y := by
          rw [isMinOn_univ_iff] at hvmin
          exact hvmin y
        exact top_le_iff.mp <| hv_top ▸ hvy
      rw [hy_top]
      exact le_top
  have hwmin : IsMinOn h Set.univ w := by
    simpa [h] using (mem_argmin_iff.mp hw_arg)
  have hw_argminOn_polar : w ∈ Argmin[Kᵒ⊖] f.asEReal∗ᵛ := by
    refine mem_argminOn_iff.mpr ⟨hw_polar, ?_⟩
    rw [isMinOn_iff]
    intro z hz
    have hwz : h w ≤ h z := by
      rw [isMinOn_univ_iff] at hwmin
      exact hwmin z
    rw [show h w = fenchelDualObjective f (ι[K]) w by rfl,
      fenchelDualObjective_indicator_eq_conjugate_neg_of_mem_polar f K hindicator_conj hw_polar,
      show h z = fenchelDualObjective f (ι[K]) z by rfl,
      fenchelDualObjective_indicator_eq_conjugate_neg_of_mem_polar f K hindicator_conj hz] at hwz
    simpa [ERealFunction.reverse] using hwz
  let u : H := -w
  have hu_arg : u ∈ Argmin[Kᵒ⊕] f.asEReal∗ :=
    neg_mem_argminOn_conjugate_of_mem_argminOn_reflectedConjugate f K hw_argminOn_polar
  have hw_eq : h w = h v := by
    rw [isMinOn_univ_iff] at hvmin hwmin
    exact le_antisymm (hwmin v) (hvmin w)
  refine ⟨u, hu_arg, ?_⟩
  calc
    sInf (f.asEReal '' K) = primalOptimalValue f (ι[K]) := by
      symm
      exact primalOptimalValue_indicator_eq_sInf_image f K
    _ = -h v := by simpa [h] using hvEq
    _ = -h w := by rw [hw_eq]
    _ = -f.asEReal∗ u := by
      rw [show h w = fenchelDualObjective f (ι[K]) w by rfl,
        fenchelDualObjective_indicator_eq_conjugate_neg_of_mem_polar f K hindicator_conj hw_polar]

end FenchelDuality

end ERealFunction
