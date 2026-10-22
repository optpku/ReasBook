/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Example_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 4.5 is `source-facing`. Its owner abstractions already exist upstream:
the indicator notation `δ_ C` / `extendedIndicator` in Chapter 2, the primal conjugate owner `f∗`
in Definition 4.1, and the
distance-based potential in Example 2.5 as `euclidean_distance_potential`. This file therefore
keeps the Fenchel-conjugacy identity specialized to that canonical project data, together with the
pointwise companion theorem used to rewrite the identity at a chosen `y`. The real-valued
distance potential is viewed as `EReal`-valued for conjugacy. -/
recall conjugate_function_primal

-- Semantic recall note: `lean_leansearch` did not surface a relevant project/mathlib owner theorem
-- for this exact distance-potential conjugacy, so the file follows the local Chapter 4 precedent
-- and states the proposition directly on the canonical primal conjugate surface `f∗`.

-- Proof sketch: rewrite `euclidean_distance_potential C` as the supremum over `c ∈ C` of the
-- affine functions `x ↦ ⟪x, c⟫ - 1/2 ‖c‖²`, identify the Euclidean pairing with the dual pairing
-- through `toDualMap`, and then compute the conjugate by splitting into the cases `y ∈ C` and
-- `y ∉ C`.
/-- Helper for Proposition 4.5: at a point `y ∈ C`, the distance potential reduces to
`‖y‖² / 2`. -/
lemma euclideanDistancePotential_eq_halfNormSq_div_two_of_mem
    (C : Set E) {y : E} (hy : y ∈ C) :
    euclidean_distance_potential C y = ‖y‖ ^ 2 / 2 := by
  -- Collapse the distance term using `d(y, C) = 0` for `y ∈ C`.
  rw [euclidean_distance_potential_apply, Metric.infDist_zero_of_mem hy]
  ring

/-- Helper for Proposition 4.5: a point outside a closed convex set admits a strictly separating
inner-product direction. -/
lemma existsStrictSeparatingInner
    (C : Set E) {y : E} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hy : y ∉ C) :
    ∃ u : E, ∃ α : ℝ, (∀ c ∈ C, inner ℝ c u < α) ∧ α < inner ℝ y u := by
  -- Convert Hahn-Banach's separating functional to a vector through the Riesz map.
  obtain ⟨p, α, hpC, hpy⟩ := geometric_hahn_banach_closed_point hC_convex hC_closed hy
  refine ⟨(InnerProductSpace.toDual ℝ E).symm p, α, ?_, ?_⟩
  · intro c hc
    have hc' : inner ℝ ((InnerProductSpace.toDual ℝ E).symm p) c = p c := by
      simpa using
        (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E) (x := c) (y := p))
    calc
      inner ℝ c ((InnerProductSpace.toDual ℝ E).symm p)
          = inner ℝ ((InnerProductSpace.toDual ℝ E).symm p) c := by
            rw [real_inner_comm]
      _ = p c := hc'
      _ < α := hpC c hc
  · have hy' : inner ℝ ((InnerProductSpace.toDual ℝ E).symm p) y = p y := by
      simpa using
        (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E) (x := y) (y := p))
    calc
      α < p y := hpy
      _ = inner ℝ ((InnerProductSpace.toDual ℝ E).symm p) y := by rw [← hy']
      _ = inner ℝ y ((InnerProductSpace.toDual ℝ E).symm p) := by rw [real_inner_comm]

/-- Helper for Proposition 4.5: along a direction whose inner products with points of `C` are
strictly below `α`, the distance potential grows at most linearly with slope `α`. -/
lemma euclideanDistancePotential_smul_le_of_strictUpperBound
    (C : Set E) (hC_nonempty : C.Nonempty) (u : E) (α t : ℝ)
    (huC : ∀ c ∈ C, inner ℝ c u < α) (ht : 0 ≤ t) :
    euclidean_distance_potential C (t • u) ≤ t * α := by
  -- Rewrite the potential as a supremum of affine witnesses and bound each witness separately.
  rw [euclidean_distance_potential_eq_sSup_affine_apply C hC_nonempty]
  refine csSup_le ?_ ?_
  · rcases hC_nonempty with ⟨c, hc⟩
    exact ⟨_, ⟨c, hc, rfl⟩⟩
  · intro z hz
    rcases hz with ⟨c, hc, rfl⟩
    change inner ℝ c (t • u) - (‖c‖ ^ 2) / 2 ≤ t * α
    rw [real_inner_smul_right]
    have hcα : inner ℝ c u ≤ α := (huC c hc).le
    have hsq : 0 ≤ ‖c‖ ^ 2 / 2 := by positivity
    nlinarith

/-- Proposition 4.5: for a nonempty closed convex set `C` in a Euclidean space, the conjugate of
`x ↦ 1/2 ‖x‖² - 1/2 d(x, C)²`, expressed through the Chapter 2 owner
`euclidean_distance_potential`, is `y ↦ 1/2 ‖y‖² + (δ_ C) y`. -/
theorem conjugate_function_quadratic_distance_eq_half_squared_norm_add_extendedIndicator
    (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ((fun x ↦ (euclidean_distance_potential C x : EReal))∗) =
      fun y ↦ (((1 / 2 : ℝ) * ‖y‖ ^ 2 : ℝ) : EReal) + (δ_ C) y := by
  funext y
  by_cases hy : y ∈ C
  · -- On `C`, the indicator vanishes, so the conjugate is the finite quadratic term.
    rw [conjugate_function_primal_apply, conjugate_function_apply, extendedIndicator_of_mem hy]
    simp only [add_zero]
    apply le_antisymm
    · refine sSup_le ?_
      intro z hz
      rcases hz with ⟨x, rfl⟩
      -- Each affine witness is bounded above by the quadratic value at `y`.
      have hreal : inner ℝ y x - euclidean_distance_potential C x ≤ (1 / 2 : ℝ) * ‖y‖ ^ 2 := by
        have hpot := affineValue_le_potential C x y hy
        nlinarith
      simpa [InnerProductSpace.toDualMap_apply_apply] using
        (show (((inner ℝ y x - euclidean_distance_potential C x : ℝ) : EReal)) ≤
            (((1 / 2 : ℝ) * ‖y‖ ^ 2 : ℝ) : EReal) from by
          exact_mod_cast hreal)
    · -- Evaluating the supremum at `x = y` gives the matching lower bound.
      have hyReal :
          (1 / 2 : ℝ) * ‖y‖ ^ 2 = inner ℝ y y - euclidean_distance_potential C y := by
        rw [real_inner_self_eq_norm_sq, euclideanDistancePotential_eq_halfNormSq_div_two_of_mem C hy]
        ring
      have hyEReal :
          ((((1 / 2 : ℝ) * ‖y‖ ^ 2 : ℝ) : EReal)) =
            (((InnerProductSpace.toDualMap ℝ E y y : ℝ) : EReal) -
              (euclidean_distance_potential C y : EReal)) := by
        exact_mod_cast hyReal
      rw [hyEReal]
      exact le_sSup ⟨y, rfl⟩
  · -- Outside `C`, a separating direction produces witnesses with arbitrarily large value.
    obtain ⟨u, α, huC, huy⟩ := existsStrictSeparatingInner C hC_closed hC_convex hy
    rw [conjugate_function_primal_apply, conjugate_function_apply, extendedIndicator_of_not_mem hy]
    rw [EReal.coe_add_top]
    rw [EReal.eq_top_iff_forall_lt]
    intro r
    let gap : ℝ := inner ℝ y u - α
    have hgap : 0 < gap := by
      dsimp [gap]
      linarith
    -- Scale the separating direction until its linear gain dominates the prescribed bound `r`.
    obtain ⟨n, hn⟩ := exists_nat_gt (r / gap)
    have hlarge : r < (n : ℝ) * gap := by
      have hmul : (r / gap) * gap < (n : ℝ) * gap := by
        exact mul_lt_mul_of_pos_right hn hgap
      have hgap_ne : gap ≠ 0 := ne_of_gt hgap
      simpa [div_eq_mul_inv, mul_assoc, hgap_ne] using hmul
    have hscaled :
        euclidean_distance_potential C ((n : ℝ) • u) ≤ (n : ℝ) * α :=
      euclideanDistancePotential_smul_le_of_strictUpperBound C hC_nonempty u α (n : ℝ) huC
        (by positivity)
    have hwitness :
        ((((n : ℝ) * gap : ℝ) : EReal)) ≤
          (((InnerProductSpace.toDualMap ℝ E y) ((n : ℝ) • u) : EReal) -
            (euclidean_distance_potential C ((n : ℝ) • u) : EReal)) := by
      -- The scaled separating gap beats the potential's linear upper bound on the same ray.
      have hreal :
          (n : ℝ) * gap ≤
            inner ℝ y ((n : ℝ) • u) - euclidean_distance_potential C ((n : ℝ) • u) := by
        have hsub :
            inner ℝ y ((n : ℝ) • u) - (n : ℝ) * α ≤
              inner ℝ y ((n : ℝ) • u) - euclidean_distance_potential C ((n : ℝ) • u) :=
          sub_le_sub_left hscaled _
        have hleft :
            (n : ℝ) * gap = inner ℝ y ((n : ℝ) • u) - (n : ℝ) * α := by
          dsimp [gap]
          rw [real_inner_smul_right]
          ring
        rw [hleft]
        exact hsub
      have hrealEReal :
          ((((n : ℝ) * gap : ℝ) : EReal)) ≤
            (((inner ℝ y ((n : ℝ) • u) -
                euclidean_distance_potential C ((n : ℝ) • u) : ℝ) : EReal)) := by
        exact_mod_cast hreal
      simpa [InnerProductSpace.toDualMap_apply_apply, real_inner_smul_right] using hrealEReal
    exact lt_of_lt_of_le
      (by exact_mod_cast hlarge)
      (le_trans hwitness (le_sSup ⟨(n : ℝ) • u, rfl⟩))

/-- Pointwise form of Proposition 4.5 on the Chapter 4 primal conjugate owner `f∗`. -/
theorem conjugate_function_quadratic_distance_apply_eq_half_squared_norm_add_extendedIndicator
    (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (y : E) :
    ((fun x ↦ (euclidean_distance_potential C x : EReal))∗) y =
      (((1 / 2 : ℝ) * ‖y‖ ^ 2 : ℝ) : EReal) + (δ_ C) y := by
  simpa using congrArg (fun f : E → EReal ↦ f y)
    (conjugate_function_quadratic_distance_eq_half_squared_norm_add_extendedIndicator
      C hC_nonempty hC_closed hC_convex)

end
