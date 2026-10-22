/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped SupportFunction

/- This item lies in the chapter's support-function intersection domain.

Primary domain:
- support functions of bounded convex sets in finite-dimensional real inner-product spaces.

Relevant owner declarations available in the proved prefix:
- `supportFunction` / `supportFunction_apply` in `Definition_3_9`
- `IsCompact.continuous_sSup` from Mathlib's compact-extreme-value API
- `geometric_hahn_banach_compact_closed` from Mathlib's compact/closed separation API

Source/core/bridge triage:
- source-facing: the textbook support-function formula for intersections
- core/canonical: `supportFunction`
- bridge/view: this numbered theorem file

The earlier recall-only wrapper depended on `Theorem_3_1_22`, but that owner theorem is still
unfinished upstream. This file therefore now carries a local proof skeleton and the closure /
compactness helpers that the source-faithful argument needs. -/

/-- Helper for Theorem 3.27 [Chapter3_2.json:22]: if `s ⊆ t ⊆ closure s`, `s` is nonempty, and
`t` is bounded above, then the two `sSup` values coincide. -/
lemma sSup_eq_of_subset_of_subset_closure
    {s t : Set EReal} (hs : s.Nonempty) (ht_bdd : BddAbove t)
    (hst : s ⊆ t) (hts : t ⊆ closure s) :
    sSup t = sSup s := by
  refine (isLUB_csSup (hs.mono hst) ht_bdd).unique ?_
  exact
    ((isLUB_iff_of_subset_of_subset_closure hst hts).1
      (isLUB_csSup hs (ht_bdd.mono hst)))

/-- Helper for Theorem 3.27 [Chapter3_2.json:22]: every point of `Q` gives a lower bound for the
support function `ξ[Q]`. -/
lemma le_supportFunction_of_mem
    {Q : Set E} {g x : E} (hg : g ∈ Q) :
    ((inner ℝ g x : ℝ) : EReal) ≤ ξ[Q] x := by
  -- Expand the support function and insert the given point into the supremum image.
  rw [supportFunction_apply]
  exact le_sSup ⟨g, hg, rfl⟩

/-- Helper for Theorem 3.27 [Chapter3_2.json:22]: on a compact index set, the support function is
continuous in its argument. -/
lemma supportFunction_continuous_of_isCompact
    {Q : Set E} (hQ_compact : IsCompact Q) :
    Continuous fun x : E ↦ ξ[Q] x := by
  let φ : E → E → EReal := fun x g ↦ ↑(inner ℝ g x)
  have hφ : Continuous ↿φ := by
    -- The uncurried pairing map is continuous, and the `ℝ → EReal` coercion preserves that.
    simpa [φ, Function.uncurry] using
      (continuous_coe_real_ereal.comp (continuous_snd.inner continuous_fst))
  -- The support function is the pointwise `sSup` of this continuous family over the compact set.
  simpa [φ, supportFunction_apply] using hQ_compact.continuous_sSup hφ

/-- Helper for Theorem 3.27 [Chapter3_2.json:22]: replacing a bounded nonempty set by its closure
does not change its support function. -/
lemma supportFunction_closure_eq_of_bounded
    [FiniteDimensional ℝ E]
    {Q : Set E} (hQ_bounded : Bornology.IsBounded Q) (hQ_nonempty : Q.Nonempty) :
    ξ[closure Q] = ξ[Q] := by
  funext x
  let φ : E → EReal := fun g ↦ ↑(inner ℝ g x)
  have hφ_cont : Continuous φ := by
    -- The slice `g ↦ ⟪g, x⟫` is continuous, and the `EReal` coercion preserves continuity.
    simpa [φ] using (continuous_coe_real_ereal.comp (continuous_id.inner continuous_const))
  rw [supportFunction_apply, supportFunction_apply]
  change sSup (φ '' closure Q) = sSup (φ '' Q)
  -- The continuous image of the closure lies in the closure of the image, so the two suprema match.
  exact sSup_eq_of_subset_of_subset_closure
    (hQ_nonempty.image φ)
    ((hQ_bounded.isCompact_closure.image hφ_cont).bddAbove)
    (by
      rintro _ ⟨g, hg, rfl⟩
      exact ⟨g, subset_closure hg, rfl⟩)
    (hφ_cont.continuousOn.image_closure)

/-- Helper for Theorem 3.27 [Chapter3_2.json:22]: the support function of a nonempty set vanishes
at the origin. -/
lemma supportFunction_zero_eq_zero_of_nonempty
    {Q : Set E} (hQ_nonempty : Q.Nonempty) :
    ξ[Q] (0 : E) = 0 := by
  rw [supportFunction_apply]
  rcases hQ_nonempty with ⟨g, hg⟩
  have himage :
      ((fun z : E ↦ ((inner ℝ z (0 : E) : ℝ) : EReal)) '' Q) = {0} := by
    ext a
    constructor
    · rintro ⟨z, hz, rfl⟩
      simp
    · intro ha
      rw [Set.mem_singleton_iff] at ha
      refine ⟨g, hg, ?_⟩
      simp [ha]
  rw [himage]
  simp

/-- Helper for Theorem 3.27 [Chapter3_2.json:22]: on a compact set, a maximizing support point
realizes the support value. -/
lemma supportFunction_eq_of_isMaxOn
    {Q : Set E} {x g : E}
    (hg : g ∈ Q)
    (hmax : IsMaxOn (fun z : E ↦ (((inner ℝ z x : ℝ)) : EReal)) Q g) :
    ξ[Q] x = ((inner ℝ g x : ℝ) : EReal) := by
  -- Rewrite the support function as the supremum of the same compact image and use the maximum.
  rw [supportFunction_apply]
  exact (hmax.isLUB hg).csSup_eq ⟨_, ⟨g, hg, rfl⟩⟩

/-- Helper for Theorem 3.27 [Chapter3_2.json:22]: on a nonempty compact set, every support value
is finite. -/
lemma supportFunction_ne_top_ne_bot_of_isCompact
    {Q : Set E} (hQ_compact : IsCompact Q) (hQ_nonempty : Q.Nonempty) (x : E) :
    ξ[Q] x ≠ ⊤ ∧ ξ[Q] x ≠ ⊥ := by
  -- A compact maximizing point rewrites the support value as a genuine real number.
  obtain ⟨g, hgQ, hmax⟩ :=
    hQ_compact.exists_isMaxOn hQ_nonempty
      (show ContinuousOn (fun z : E ↦ inner ℝ z x) Q from by fun_prop)
  have hmaxE :
      IsMaxOn (fun z : E ↦ (((inner ℝ z x : ℝ)) : EReal)) Q g := by
    intro z hz
    show (((inner ℝ z x : ℝ)) : EReal) ≤ (((inner ℝ g x : ℝ)) : EReal)
    exact_mod_cast hmax hz
  have hξ : ξ[Q] x = ((inner ℝ g x : ℝ) : EReal) :=
    supportFunction_eq_of_isMaxOn hgQ hmaxE
  constructor
  · rw [hξ]
    exact EReal.coe_ne_top _
  · rw [hξ]
    exact EReal.coe_ne_bot _

/-- Helper for Theorem 3.27 [Chapter3_2.json:22]: a closed ball inside `K₁ ∩ K₂` gives a
coercive linear lower bound for the translated support-function sum. -/
lemma supportFunction_sum_lower_bound_of_closedBall_subset_inter
    {K₁ K₂ : Set E} {c x : E} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hball : Metric.closedBall c ρ ⊆ K₁ ∩ K₂) :
    ∀ y : E,
      (((inner ℝ c x - ρ * ‖x‖ + 2 * ρ * ‖y‖ : ℝ)) : EReal) ≤
        ξ[K₁] (x + y) + ξ[K₂] (-y) := by
  intro y
  let u : E := NormedSpace.normalize y
  have hu_norm_le : ‖u‖ ≤ 1 := by
    -- The normalized direction always stays in the unit closed ball.
    by_cases hy : y = 0
    · simp [u, hy]
    · simpa [u] using (NormedSpace.norm_normalize_eq_one_iff.mpr hy).le
  have hu_mem₁ : c + ρ • u ∈ K₁ := by
    have hmem : c + ρ • u ∈ Metric.closedBall c ρ := by
      -- The displaced center stays inside the radius-`ρ` closed ball because `‖u‖ ≤ 1`.
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hsub : c + ρ • u - c = ρ • u := by
        abel_nf
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ]
      nlinarith
    exact (hball hmem).1
  have hu_mem₂ : c - ρ • u ∈ K₂ := by
    have hmem : c - ρ • u ∈ Metric.closedBall c ρ := by
      -- The opposite displaced center satisfies the same norm bound.
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hsub : c - ρ • u - c = -(ρ • u) := by
        simp [sub_eq_add_neg, add_comm, add_left_comm, u]
      rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ]
      nlinarith
    exact (hball hmem).2
  have huy : inner ℝ u y = ‖y‖ := by
    -- The normalized direction pairs with `y` exactly by the norm of `y`.
    by_cases hy : y = 0
    · simp [u, hy]
    · have hsmul := NormedSpace.norm_smul_normalize y
      calc
        inner ℝ u y = inner ℝ (NormedSpace.normalize y) y := by rfl
        _ = inner ℝ (NormedSpace.normalize y) (‖y‖ • NormedSpace.normalize y) := by rw [hsmul]
        _ = ‖y‖ * inner ℝ (NormedSpace.normalize y) (NormedSpace.normalize y) := by
              rw [inner_smul_right]
        _ = ‖y‖ := by
              rw [inner_self_eq_norm_sq_to_K]
              simp [NormedSpace.norm_normalize, hy]
  have hlow_inner : -‖x‖ ≤ inner ℝ u x := by
    -- Cauchy--Schwarz bounds the `u`-component of `x` from below because `‖u‖ ≤ 1`.
    have habs : |inner ℝ u x| ≤ ‖u‖ * ‖x‖ := abs_real_inner_le_norm u x
    have hlow' : -(‖u‖ * ‖x‖) ≤ inner ℝ u x := (abs_le.mp habs).1
    nlinarith [hlow', hu_norm_le, norm_nonneg x]
  have hexpand₁ :
      inner ℝ (c + ρ • u) (x + y) =
        inner ℝ c x + inner ℝ c y + ρ * inner ℝ u x + ρ * inner ℝ u y := by
    -- Expand the first translated pairing into its `x` and `y` pieces.
    rw [inner_add_left, inner_add_right, inner_smul_left, inner_add_right]
    simp
    ring
  have hexpand₂ :
      inner ℝ (c - ρ • u) (-y) = -inner ℝ c y + ρ * inner ℝ u y := by
    -- Expand the second translated pairing and absorb the minus signs.
    rw [sub_eq_add_neg, inner_add_left, inner_neg_left, inner_neg_right,
      inner_smul_left, inner_neg_right]
    simp
  calc
    (((inner ℝ c x - ρ * ‖x‖ + 2 * ρ * ‖y‖ : ℝ)) : EReal)
        ≤ ((inner ℝ (c + ρ • u) (x + y) : ℝ) : EReal) +
            ((inner ℝ (c - ρ • u) (-y) : ℝ) : EReal) := by
              -- The explicit ball test points realize the desired coercive lower bound.
              rw [← EReal.coe_add]
              have hreal :
                  inner ℝ c x - ρ * ‖x‖ + 2 * ρ * ‖y‖ ≤
                    inner ℝ (c + ρ • u) (x + y) + inner ℝ (c - ρ • u) (-y) := by
                calc
                  inner ℝ c x - ρ * ‖x‖ + 2 * ρ * ‖y‖
                      ≤ inner ℝ c x + ρ * inner ℝ u x + 2 * ρ * ‖y‖ := by
                            nlinarith [hρ, hlow_inner]
                  _ = inner ℝ (c + ρ • u) (x + y) + inner ℝ (c - ρ • u) (-y) := by
                        rw [hexpand₁, hexpand₂, huy]
                        ring
              exact_mod_cast hreal
    _ ≤ ξ[K₁] (x + y) + ξ[K₂] (-y) := by
          exact add_le_add
            (le_supportFunction_of_mem hu_mem₁)
            (le_supportFunction_of_mem hu_mem₂)

/-- Helper for Theorem 3.27 [Chapter3_2.json:22]: once a positive closed ball lies in
`K₁ ∩ K₂`, the finite real surface of the compact translated support-function sum attains a global
minimum. -/
lemma exists_isMinOn_supportFunction_sum_of_closedBall_subset_inter
    [FiniteDimensional ℝ E]
    {K₁ K₂ : Set E} (hK₁_compact : IsCompact K₁) (hK₂_compact : IsCompact K₂)
    {c x : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.closedBall c ρ ⊆ K₁ ∩ K₂) :
    ∃ yStar : E,
      IsMinOn
        (fun y : E ↦ (ξ[K₁] (x + y)).toReal + (ξ[K₂] (-y)).toReal)
        Set.univ yStar := by
  have hc_mem : c ∈ Metric.closedBall c ρ := by
    -- The center of a closed ball belongs to that ball because `ρ > 0`.
    simp [Metric.mem_closedBall, hρ.le]
  have hK₁_nonempty : K₁.Nonempty := by
    -- The common closed ball witness gives a concrete point of `K₁`.
    refine ⟨c, ?_⟩
    exact (hball hc_mem).1
  have hK₂_nonempty : K₂.Nonempty := by
    -- The same closed-ball center also belongs to `K₂`.
    refine ⟨c, ?_⟩
    exact (hball hc_mem).2
  let ψ : E → ℝ := fun y ↦ (ξ[K₁] (x + y)).toReal + (ξ[K₂] (-y)).toReal
  have hψ₁_cont : Continuous fun y : E ↦ (ξ[K₁] (x + y)).toReal := by
    -- Compactness makes the support function continuous, and bounded nonemptiness makes it finite.
    exact ContinuousOn.comp_continuous EReal.continuousOn_toReal
      ((supportFunction_continuous_of_isCompact hK₁_compact).comp
        (continuous_const.add continuous_id))
      (fun y ↦ by
        have hy := supportFunction_ne_top_ne_bot_of_isCompact hK₁_compact hK₁_nonempty (x + y)
        intro hmem
        rcases hmem with hmem | hmem
        · exact hy.2 hmem
        · exact hy.1 hmem)
  have hψ₂_cont : Continuous fun y : E ↦ (ξ[K₂] (-y)).toReal := by
    -- The second term is the same finite compact support function composed with negation.
    exact ContinuousOn.comp_continuous EReal.continuousOn_toReal
      ((supportFunction_continuous_of_isCompact hK₂_compact).comp continuous_neg)
      (fun y ↦ by
        have hy := supportFunction_ne_top_ne_bot_of_isCompact hK₂_compact hK₂_nonempty (-y)
        intro hmem
        rcases hmem with hmem | hmem
        · exact hy.2 hmem
        · exact hy.1 hmem)
  have hψ_cont : Continuous ψ := by
    -- The real objective is a sum of the two continuous finite support-function terms.
    exact hψ₁_cont.add hψ₂_cont
  have hlower_real :
      ∀ y : E, inner ℝ c x - ρ * ‖x‖ + 2 * ρ * ‖y‖ ≤ ψ y := by
    intro y
    -- Convert the established `EReal` coercive bound into the real surface via `toReal`.
    have hcoercive :=
      supportFunction_sum_lower_bound_of_closedBall_subset_inter
        (K₁ := K₁) (K₂ := K₂) (c := c) (x := x) (ρ := ρ) hρ.le hball y
    have hK₁y := supportFunction_ne_top_ne_bot_of_isCompact hK₁_compact hK₁_nonempty (x + y)
    have hK₂y := supportFunction_ne_top_ne_bot_of_isCompact hK₂_compact hK₂_nonempty (-y)
    have hsum_ne_top : ξ[K₁] (x + y) + ξ[K₂] (-y) ≠ ⊤ :=
      EReal.add_ne_top hK₁y.1 hK₂y.1
    have hcoercive' :
        (((inner ℝ c x - ρ * ‖x‖ + 2 * ρ * ‖y‖ : ℝ)) : EReal) ≤
          ξ[K₁] (x + y) + ξ[K₂] (-y) := by
      exact hcoercive
    have hcoercive_real :
        ((((inner ℝ c x - ρ * ‖x‖ + 2 * ρ * ‖y‖ : ℝ)) : EReal)).toReal ≤
          (ξ[K₁] (x + y) + ξ[K₂] (-y)).toReal := by
      exact
        EReal.toReal_le_toReal hcoercive'
          (EReal.coe_ne_bot (inner ℝ c x - ρ * ‖x‖ + 2 * ρ * ‖y‖ : ℝ))
          hsum_ne_top
    have hcoercive_real' :
        ((((inner ℝ c x - ρ * ‖x‖ + 2 * ρ * ‖y‖ : ℝ)) : EReal)).toReal ≤ ψ y := by
      change ((((inner ℝ c x - ρ * ‖x‖ + 2 * ρ * ‖y‖ : ℝ)) : EReal)).toReal ≤
        (ξ[K₁] (x + y)).toReal + (ξ[K₂] (-y)).toReal
      rw [← EReal.toReal_add hK₁y.1 hK₁y.2 hK₂y.1 hK₂y.2]
      exact hcoercive_real
    exact_mod_cast hcoercive_real'
  have hsublevel_bounded : Bornology.IsBounded {y : E | ψ y ≤ ψ 0} := by
    let A : ℝ := inner ℝ c x - ρ * ‖x‖
    have hA_le : A ≤ ψ 0 := by
      -- Evaluating the coercive estimate at `0` gives the baseline lower bound.
      simpa [A, ψ] using hlower_real (0 : E)
    let R : ℝ := (ψ 0 - A) / (2 * ρ)
    refine (Metric.isBounded_iff_subset_closedBall (0 : E)).2 ?_
    refine ⟨R, ?_⟩
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hbound : A + 2 * ρ * ‖y‖ ≤ ψ 0 := (hlower_real y).trans hy
    have hden : 0 < 2 * ρ := by
      nlinarith
    have hnorm_mul : (2 * ρ) * ‖y‖ ≤ ψ 0 - A := by
      nlinarith
    have hnorm : ‖y‖ ≤ R := by
      dsimp [R]
      exact (le_div_iff₀ hden).2 (by simpa [mul_comm] using hnorm_mul)
    simpa using hnorm
  obtain ⟨yStar, hyStar⟩ := hψ_cont.exists_forall_le_of_isBounded (0 : E) hsublevel_bounded
  -- The extreme-value theorem on the bounded sublevel set packages the desired global minimizer.
  refine ⟨yStar, ?_⟩
  simpa [ψ, isMinOn_univ_iff] using hyStar

/-- Helper for Theorem 3.27 [Chapter3_2.json:22]: on a nonempty compact set, the active support
face at `u` is nonempty and compact. -/
lemma supportFunction_active_face_nonempty_compact
    [FiniteDimensional ℝ E]
    {K : Set E} (hK_compact : IsCompact K) (hK_nonempty : K.Nonempty) {u : E} :
    ({g : E | g ∈ K ∧ inner ℝ g u = (ξ[K] u).toReal}).Nonempty ∧
      IsCompact {g : E | g ∈ K ∧ inner ℝ g u = (ξ[K] u).toReal} := by
  obtain ⟨gMax, hgMax, hmax⟩ :=
    hK_compact.exists_isMaxOn hK_nonempty
      (show ContinuousOn (fun z : E ↦ inner ℝ z u) K from by fun_prop)
  have hmaxE :
      IsMaxOn (fun z : E ↦ (((inner ℝ z u : ℝ)) : EReal)) K gMax := by
    intro z hz
    show (((inner ℝ z u : ℝ)) : EReal) ≤ (((inner ℝ gMax u : ℝ)) : EReal)
    exact_mod_cast hmax hz
  have hξ :
      ξ[K] u = ((inner ℝ gMax u : ℝ) : EReal) :=
    supportFunction_eq_of_isMaxOn hgMax hmaxE
  have hg_active : gMax ∈ {g : E | g ∈ K ∧ inner ℝ g u = (ξ[K] u).toReal} := by
    -- A compact maximizer exposes the support value, so it belongs to the active face.
    refine ⟨hgMax, ?_⟩
    rw [hξ, EReal.toReal_coe]
  have hlevel_closed : IsClosed {g : E | inner ℝ g u = (ξ[K] u).toReal} := by
    -- The active-face equality cuts out a closed affine nesterovHyperplane.
    exact isClosed_eq (by fun_prop) continuous_const
  have hface_compact :
      IsCompact (K ∩ {g : E | inner ℝ g u = (ξ[K] u).toReal}) :=
    hK_compact.inter_right hlevel_closed
  constructor
  · exact ⟨gMax, hg_active⟩
  · simpa [Set.setOf_and, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hface_compact

/-- Helper for Theorem 3.27 [Chapter3_2.json:22]: the active support face of a convex set is
convex. -/
lemma supportFunction_active_face_convex
    {K : Set E} (hK_convex : Convex ℝ K) {u : E} :
    Convex ℝ {g : E | g ∈ K ∧ inner ℝ g u = (ξ[K] u).toReal} := by
  have hhyperplane :
      Convex ℝ {g : E | inner ℝ g u = (ξ[K] u).toReal} := by
    have hlin : IsLinearMap ℝ (fun g : E ↦ inner ℝ g u) := by
      refine ⟨?_, ?_⟩
      · intro x y
        simp [inner_add_left]
      · intro c x
        simp [inner_smul_left]
    simpa using convex_hyperplane hlin (ξ[K] u).toReal
  simpa [Set.setOf_and, Set.inter_comm] using hK_convex.inter hhyperplane

/-- Helper for Theorem 3.27 [Chapter3_2.json:22]: if every active support point at `u` has
directional slope strictly below `a`, then the support function admits a strict linear upper bound
near `u` in direction `d`. -/
lemma supportFunction_local_upper_linearization_of_active_face_real
    [FiniteDimensional ℝ E]
    {K : Set E} (hK_compact : IsCompact K) (hK_nonempty : K.Nonempty)
    {u d : E} {a : ℝ}
    (ha : ∀ g ∈ {g : E | g ∈ K ∧ inner ℝ g u = (ξ[K] u).toReal}, inner ℝ g d < a) :
    ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
      (ξ[K] (u + t • d)).toReal < (ξ[K] u).toReal + t * a := by
  obtain ⟨uMax, huMax, hmax_u⟩ :=
    hK_compact.exists_isMaxOn hK_nonempty
      (show ContinuousOn (fun z : E ↦ inner ℝ z u) K from by fun_prop)
  have hmax_uE :
      IsMaxOn (fun z : E ↦ (((inner ℝ z u : ℝ)) : EReal)) K uMax := by
    intro z hz
    show (((inner ℝ z u : ℝ)) : EReal) ≤ (((inner ℝ uMax u : ℝ)) : EReal)
    exact_mod_cast hmax_u hz
  have hξu :
      ξ[K] u = ((inner ℝ uMax u : ℝ) : EReal) :=
    supportFunction_eq_of_isMaxOn huMax hmax_uE
  have hξu_real : (ξ[K] u).toReal = inner ℝ uMax u := by
    rw [hξu, EReal.toReal_coe]
  let F : Set E := {g : E | g ∈ K ∧ inner ℝ g u = (ξ[K] u).toReal}
  have hF_nonempty : F.Nonempty :=
    (supportFunction_active_face_nonempty_compact
      (K := K) hK_compact hK_nonempty).1
  have hF_compact : IsCompact F :=
    (supportFunction_active_face_nonempty_compact
      (K := K) hK_compact hK_nonempty).2
  let slope : E → ℝ := fun g ↦ inner ℝ g d
  obtain ⟨gFace, hgFace, hmax_face⟩ :=
    hF_compact.exists_isMaxOn hF_nonempty
      (show ContinuousOn slope F from by
        dsimp [slope]
        fun_prop)
  have hmax_face_lt : slope gFace < a := ha gFace hgFace
  let b : ℝ := (slope gFace + a) / 2
  have hb_lt : b < a := by
    dsimp [b]
    linarith
  have hF_subset_open :
      F ⊆ {g : E | slope g < b} := by
    intro g hg
    have hg_le : slope g ≤ slope gFace := hmax_face hg
    have hface_lt_mid : slope gFace < b := by
      dsimp [b]
      linarith
    exact lt_of_le_of_lt hg_le hface_lt_mid
  have hopen : IsOpen {g : E | slope g < b} := by
    dsimp [slope, b]
    exact isOpen_lt (by fun_prop) continuous_const
  let C : Set E := K \ {g : E | slope g < b}
  have hC_compact : IsCompact C := by
    -- The complement of the open slope neighborhood is compact inside `K`.
    dsimp [C]
    exact hK_compact.inter_right hopen.isClosed_compl
  obtain ⟨gSlope, hgSlope, hmax_slope⟩ :=
    hK_compact.exists_isMaxOn hK_nonempty
      (show ContinuousOn slope K from by
        dsimp [slope]
        fun_prop)
  let qBound : ℝ := max 0 (slope gSlope - a)
  have hqBound_nonneg : 0 ≤ qBound := by
    dsimp [qBound]
    exact le_max_left _ _
  have hqBound_ge :
      ∀ g ∈ K, slope g - a ≤ qBound := by
    intro g hg
    have hg_le : slope g ≤ slope gSlope := hmax_slope hg
    calc
      slope g - a ≤ slope gSlope - a := by
        linarith
      _ ≤ qBound := by
        dsimp [qBound]
        exact le_max_right _ _
  by_cases hC_empty : C = ∅
  · refine ⟨1, by positivity, ?_⟩
    intro t ht_pos htε
    obtain ⟨w, hwK, hmax_w⟩ :=
      hK_compact.exists_isMaxOn hK_nonempty
        (show ContinuousOn (fun z : E ↦ inner ℝ z (u + t • d)) K from by fun_prop)
    have hmax_wE :
        IsMaxOn (fun z : E ↦ (((inner ℝ z (u + t • d) : ℝ)) : EReal)) K w := by
      intro z hz
      show (((inner ℝ z (u + t • d) : ℝ)) : EReal) ≤
        (((inner ℝ w (u + t • d) : ℝ)) : EReal)
      exact_mod_cast hmax_w hz
    have hξut :
        ξ[K] (u + t • d) = ((inner ℝ w (u + t • d) : ℝ) : EReal) :=
      supportFunction_eq_of_isMaxOn hwK hmax_wE
    have hξut_real : (ξ[K] (u + t • d)).toReal = inner ℝ w (u + t • d) := by
      rw [hξut, EReal.toReal_coe]
    have hw_open : w ∈ {g : E | slope g < b} := by
      by_contra hw_not
      have hwC : w ∈ C := ⟨hwK, hw_not⟩
      simp [C, hC_empty] at hwC
    have hw_u_le : inner ℝ w u ≤ (ξ[K] u).toReal := by
      rw [hξu_real]
      exact hmax_u hwK
    have hw_slope_lt : slope w < b := hw_open
    have hsum_lt :
        inner ℝ w u + t * slope w < (ξ[K] u).toReal + t * b := by
      have hmul_lt : t * slope w < t * b := by
        exact mul_lt_mul_of_pos_left hw_slope_lt ht_pos
      linarith
    calc
      (ξ[K] (u + t • d)).toReal = inner ℝ w u + t * slope w := by
        rw [hξut_real, inner_add_right, inner_smul_right]
      _ < (ξ[K] u).toReal + t * b := hsum_lt
      _ < (ξ[K] u).toReal + t * a := by
        nlinarith [ht_pos, hb_lt]
  · have hC_nonempty : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hC_empty
    obtain ⟨gC, hgC, hmax_C⟩ :=
      hC_compact.exists_isMaxOn hC_nonempty
        (show ContinuousOn (fun z : E ↦ inner ℝ z u) C from by fun_prop)
    have hgC_not_active : gC ∉ F := by
      intro hgF
      have hgOpen : gC ∈ {g : E | slope g < b} := hF_subset_open hgF
      exact hgC.2 hgOpen
    have hgC_le : inner ℝ gC u ≤ (ξ[K] u).toReal := by
      rw [hξu_real]
      exact hmax_u hgC.1
    have hgC_ne : inner ℝ gC u ≠ (ξ[K] u).toReal := by
      intro hEq
      exact hgC_not_active ⟨hgC.1, hEq⟩
    have hgC_lt : inner ℝ gC u < (ξ[K] u).toReal := lt_of_le_of_ne hgC_le hgC_ne
    let δ : ℝ := (ξ[K] u).toReal - inner ℝ gC u
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      linarith
    have hδ : ∀ g ∈ C, inner ℝ g u ≤ (ξ[K] u).toReal - δ := by
      intro g hg
      have hg_le : inner ℝ g u ≤ inner ℝ gC u := hmax_C hg
      dsimp [δ]
      linarith
    let ε : ℝ := min 1 (δ / (qBound + 1))
    have hε_pos : 0 < ε := by
      refine lt_min (by positivity) ?_
      have hden : 0 < qBound + 1 := by
        linarith
      exact div_pos hδ_pos hden
    refine ⟨ε, hε_pos, ?_⟩
    intro t ht_pos htε
    obtain ⟨w, hwK, hmax_w⟩ :=
      hK_compact.exists_isMaxOn hK_nonempty
        (show ContinuousOn (fun z : E ↦ inner ℝ z (u + t • d)) K from by fun_prop)
    have hmax_wE :
        IsMaxOn (fun z : E ↦ (((inner ℝ z (u + t • d) : ℝ)) : EReal)) K w := by
      intro z hz
      show (((inner ℝ z (u + t • d) : ℝ)) : EReal) ≤
        (((inner ℝ w (u + t • d) : ℝ)) : EReal)
      exact_mod_cast hmax_w hz
    have hξut :
        ξ[K] (u + t • d) = ((inner ℝ w (u + t • d) : ℝ) : EReal) :=
      supportFunction_eq_of_isMaxOn hwK hmax_wE
    have hξut_real : (ξ[K] (u + t • d)).toReal = inner ℝ w (u + t • d) := by
      rw [hξut, EReal.toReal_coe]
    by_cases hw_open : w ∈ {g : E | slope g < b}
    · have hw_u_le : inner ℝ w u ≤ (ξ[K] u).toReal := by
        rw [hξu_real]
        exact hmax_u hwK
      have hw_slope_lt : slope w < b := hw_open
      have hsum_lt :
          inner ℝ w u + t * slope w < (ξ[K] u).toReal + t * b := by
        have hmul_lt : t * slope w < t * b := by
          exact mul_lt_mul_of_pos_left hw_slope_lt ht_pos
        linarith
      calc
        (ξ[K] (u + t • d)).toReal = inner ℝ w u + t * slope w := by
          rw [hξut_real, inner_add_right, inner_smul_right]
        _ < (ξ[K] u).toReal + t * b := hsum_lt
        _ < (ξ[K] u).toReal + t * a := by
          nlinarith [ht_pos, hb_lt]
    · have hwC : w ∈ C := ⟨hwK, hw_open⟩
      have ht_small : t < δ / (qBound + 1) := by
        exact lt_of_lt_of_le htε (min_le_right _ _)
      have hden : 0 < qBound + 1 := by
        linarith
      have ht_mul : t * qBound < δ := by
        have ht_mul' : t * (qBound + 1) < δ := by
          exact (lt_div_iff₀ hden).mp ht_small
        nlinarith [ht_mul', hqBound_nonneg, ht_pos]
      have hw_slope_bound : slope w - a ≤ qBound := hqBound_ge w hwK
      have hw_u_gap : inner ℝ w u ≤ (ξ[K] u).toReal - δ := hδ w hwC
      have ht_aux : t * (slope w - a) < δ := by
        nlinarith [ht_mul, hw_slope_bound, ht_pos]
      calc
        (ξ[K] (u + t • d)).toReal = inner ℝ w u + t * slope w := by
          rw [hξut_real, inner_add_right, inner_smul_right]
        _ = (inner ℝ w u + t * a) + t * (slope w - a) := by
          ring
        _ < ((ξ[K] u).toReal - δ + t * a) + δ := by
          nlinarith
        _ = (ξ[K] u).toReal + t * a := by
          ring

/-- Helper for Theorem 3.27 [Chapter3_2.json:22]: a real minimizer of the translated support
sum on compact convex sets yields a common active support point. -/
lemma common_active_support_point_of_isMinOn_supportFunction_sum_real
    [FiniteDimensional ℝ E]
    {K₁ K₂ : Set E}
    (hK₁_compact : IsCompact K₁) (hK₁_nonempty : K₁.Nonempty)
    (hK₂_compact : IsCompact K₂) (hK₂_nonempty : K₂.Nonempty)
    (hK₁_convex : Convex ℝ K₁) (hK₂_convex : Convex ℝ K₂)
    {x yStar : E}
    (hyStar :
      IsMinOn
        (fun y : E ↦ (ξ[K₁] (x + y)).toReal + (ξ[K₂] (-y)).toReal)
        Set.univ yStar) :
    ∃ g, g ∈ K₁ ∩ K₂ ∧
      inner ℝ g (x + yStar) = (ξ[K₁] (x + yStar)).toReal ∧
      inner ℝ g (-yStar) = (ξ[K₂] (-yStar)).toReal := by
  let F₁ : Set E := {g : E | g ∈ K₁ ∧ inner ℝ g (x + yStar) = (ξ[K₁] (x + yStar)).toReal}
  let F₂ : Set E := {g : E | g ∈ K₂ ∧ inner ℝ g (-yStar) = (ξ[K₂] (-yStar)).toReal}
  have hF₁_nonempty : F₁.Nonempty :=
    (supportFunction_active_face_nonempty_compact
      (K := K₁) hK₁_compact hK₁_nonempty).1
  have hF₂_nonempty : F₂.Nonempty :=
    (supportFunction_active_face_nonempty_compact
      (K := K₂) hK₂_compact hK₂_nonempty).1
  have hF₁_compact : IsCompact F₁ :=
    (supportFunction_active_face_nonempty_compact
      (K := K₁) hK₁_compact hK₁_nonempty).2
  have hF₂_compact : IsCompact F₂ :=
    (supportFunction_active_face_nonempty_compact
      (K := K₂) hK₂_compact hK₂_nonempty).2
  have hF₁_convex : Convex ℝ F₁ :=
    supportFunction_active_face_convex (K := K₁) hK₁_convex
  have hF₂_convex : Convex ℝ F₂ :=
    supportFunction_active_face_convex (K := K₂) hK₂_convex
  have hfaces_inter : ∃ g, g ∈ F₁ ∩ F₂ := by
    by_contra hinter
    have hdisj : Disjoint F₁ F₂ := by
      rw [Set.disjoint_iff_inter_eq_empty]
      exact Set.eq_empty_iff_forall_notMem.2 fun g hg ↦ hinter ⟨g, hg⟩
    obtain ⟨f, u, v, hF₁_lt, huv, hF₂_lt⟩ :=
      geometric_hahn_banach_compact_closed
        hF₁_convex hF₁_compact hF₂_convex hF₂_compact.isClosed hdisj
    let d : E := (InnerProductSpace.toDual ℝ E).symm f
    let a : ℝ := (u + v) / 2
    have hF₁_dir : ∀ g ∈ F₁, inner ℝ g d < a := by
      intro g hg
      have hg_lt : f g < u := hF₁_lt g hg
      have hu_mid : u < a := by
        dsimp [a]
        linarith
      have : inner ℝ d g < a := by
        simpa [d] using hg_lt.trans hu_mid
      simpa [real_inner_comm] using this
    have hF₂_dir : ∀ g ∈ F₂, inner ℝ g (-d) < -a := by
      intro g hg
      have hg_gt : v < f g := hF₂_lt g hg
      have ha_v : a < v := by
        dsimp [a]
        linarith
      have : a < inner ℝ d g := by
        simpa [d] using ha_v.trans hg_gt
      have : inner ℝ g d > a := by
        simpa [real_inner_comm] using this
      simpa [inner_neg_right] using neg_lt_neg this
    obtain ⟨ε₁, hε₁_pos, hε₁⟩ :=
      supportFunction_local_upper_linearization_of_active_face_real
        (K := K₁) hK₁_compact hK₁_nonempty
        (u := x + yStar) (d := d) (a := a) hF₁_dir
    obtain ⟨ε₂, hε₂_pos, hε₂⟩ :=
      supportFunction_local_upper_linearization_of_active_face_real
        (K := K₂) hK₂_compact hK₂_nonempty
        (u := -yStar) (d := -d) (a := -a) hF₂_dir
    let t : ℝ := min ε₁ ε₂ / 2
    have ht_pos : 0 < t := by
      dsimp [t]
      have : 0 < min ε₁ ε₂ := lt_min hε₁_pos hε₂_pos
      linarith
    have ht₁ : t < ε₁ := by
      dsimp [t]
      have hmin_pos : 0 < min ε₁ ε₂ := lt_min hε₁_pos hε₂_pos
      have hhalf_lt : min ε₁ ε₂ / 2 < min ε₁ ε₂ := by
        linarith
      exact lt_of_lt_of_le hhalf_lt (min_le_left _ _)
    have ht₂ : t < ε₂ := by
      dsimp [t]
      have hmin_pos : 0 < min ε₁ ε₂ := lt_min hε₁_pos hε₂_pos
      have hhalf_lt : min ε₁ ε₂ / 2 < min ε₁ ε₂ := by
        linarith
      exact lt_of_lt_of_le hhalf_lt (min_le_right _ _)
    have hterm₁ :
        (ξ[K₁] (x + (yStar + t • d))).toReal <
          (ξ[K₁] (x + yStar)).toReal + t * a := by
      -- The separator direction strictly lowers the first support term.
      simpa [add_assoc, add_left_comm, add_comm] using hε₁ t ht_pos ht₁
    have hterm₂ :
        (ξ[K₂] (-(yStar + t • d))).toReal <
          (ξ[K₂] (-yStar)).toReal + t * (-a) := by
      -- The opposite direction strictly lowers the second support term.
      simpa [add_assoc, add_left_comm, add_comm, smul_neg, sub_eq_add_neg] using hε₂ t ht_pos ht₂
    have hdecrease :
        (ξ[K₁] (x + (yStar + t • d))).toReal + (ξ[K₂] (-(yStar + t • d))).toReal <
          (ξ[K₁] (x + yStar)).toReal + (ξ[K₂] (-yStar)).toReal := by
      linarith
    have hyStar_le :=
      (isMinOn_univ_iff.mp hyStar) (yStar + t • d)
    exact (not_lt_of_ge hyStar_le) hdecrease
  rcases hfaces_inter with ⟨g, hgF₁, hgF₂⟩
  exact ⟨g, ⟨hgF₁.1, hgF₂.1⟩, hgF₁.2, hgF₂.2⟩

/-- Theorem 3.27 [Chapter3_2.json:22]: for bounded convex sets `Q₁` and `Q₂` with nonempty
interior intersection in a finite-dimensional real inner-product space, the support function of
`Q₁ ∩ Q₂` at `x` is the minimum over translated support-function sums
`ξ[Q₁] (x + y) + ξ[Q₂] (-y)`. -/
-- Proof sketch: first reduce to the compact convex closures `closure Q₁` and `closure Q₂`, since
-- support functions are closure-invariant. The easy inequality
-- `ξ[Q₁ ∩ Q₂] x ≤ ξ[Q₁] (x + y) + ξ[Q₂] (-y)` comes from testing against any common point
-- `g ∈ Q₁ ∩ Q₂`. The remaining source-faithful steps are: prove coercive attainment for the
-- translated-sum objective using the interior-ball witness inside `Q₁ ∩ Q₂`, then show that a
-- minimizing point has intersecting active support faces, which yields the reverse inequality.
theorem supportFunction_inter_isLeast_add_supportFunction
    [FiniteDimensional ℝ E]
    {Q₁ Q₂ : Set E}
    (hQ₁_bounded : Bornology.IsBounded Q₁) (hQ₁_convex : Convex ℝ Q₁)
    (hQ₂_bounded : Bornology.IsBounded Q₂) (hQ₂_convex : Convex ℝ Q₂)
    (hQ_int : (interior (Q₁ ∩ Q₂)).Nonempty) (x : E) :
    IsLeast
      (Set.range fun y : E ↦ ξ[Q₁] (x + y) + ξ[Q₂] (-y))
      (ξ[Q₁ ∩ Q₂] x) := by
  let φ : E → EReal := fun y ↦ ξ[Q₁] (x + y) + ξ[Q₂] (-y)
  have hQ_nonempty : (Q₁ ∩ Q₂).Nonempty := by
    rcases hQ_int with ⟨g, hg⟩
    exact ⟨g, interior_subset hg⟩
  have hQ₁_nonempty : Q₁.Nonempty := hQ_nonempty.mono Set.inter_subset_left
  have hQ₂_nonempty : Q₂.Nonempty := hQ_nonempty.mono Set.inter_subset_right
  have hlower : ∀ y : E, ξ[Q₁ ∩ Q₂] x ≤ φ y := by
    intro y
    rw [supportFunction_apply]
    refine sSup_le ?_
    rintro _ ⟨g, hg, rfl⟩
    have hg₁ : g ∈ Q₁ := hg.1
    have hg₂ : g ∈ Q₂ := hg.2
    calc
      ((inner ℝ g x : ℝ) : EReal)
          = ((inner ℝ g (x + y) : ℝ) : EReal) + ((inner ℝ g (-y) : ℝ) : EReal) := by
              rw [← EReal.coe_add]
              congr 1
              rw [inner_add_right, inner_neg_right]
              ring
      _ ≤ ξ[Q₁] (x + y) + ξ[Q₂] (-y) := by
            exact add_le_add
              (le_supportFunction_of_mem hg₁)
              (le_supportFunction_of_mem hg₂)
  let K₁ : Set E := closure Q₁
  let K₂ : Set E := closure Q₂
  have hξK₁ : ξ[K₁] = ξ[Q₁] := by
    simpa [K₁] using supportFunction_closure_eq_of_bounded hQ₁_bounded hQ₁_nonempty
  have hξK₂ : ξ[K₂] = ξ[Q₂] := by
    simpa [K₂] using supportFunction_closure_eq_of_bounded hQ₂_bounded hQ₂_nonempty
  have hξ_inter :
      ξ[closure (Q₁ ∩ Q₂)] = ξ[Q₁ ∩ Q₂] := by
    simpa using
      supportFunction_closure_eq_of_bounded
        (Q := Q₁ ∩ Q₂)
        (Bornology.IsBounded.subset hQ₁_bounded Set.inter_subset_left)
        hQ_nonempty
  have hK_int : (interior (K₁ ∩ K₂)).Nonempty := by
    -- Passing to closures only enlarges the intersection, so the interior witness persists.
    refine Set.Nonempty.mono ?_ hQ_int
    exact interior_mono <| Set.inter_subset_inter subset_closure subset_closure
  rcases hK_int with ⟨c, hc⟩
  rcases Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hc) with ⟨r, hr, hball_open⟩
  have hclosedBall :
      Metric.closedBall c (r / 2) ⊆ K₁ ∩ K₂ := by
    -- Shrinking the interior ball lets us work with a closed ball inside the compact closures.
    intro y hy
    exact interior_subset (hball_open (Metric.closedBall_subset_ball (by linarith) hy))
  have hcoercive :
      ∀ y : E,
        (((inner ℝ c x - (r / 2) * ‖x‖ + r * ‖y‖ : ℝ)) : EReal) ≤
          ξ[K₁] (x + y) + ξ[K₂] (-y) := by
    -- The closed-ball helper is the verified coercive half of the source proof.
    simpa [two_mul, mul_assoc, mul_left_comm, mul_comm] using
      supportFunction_sum_lower_bound_of_closedBall_subset_inter
        (K₁ := K₁) (K₂ := K₂) (c := c) (x := x) (ρ := r / 2)
        (by linarith)
        hclosedBall
  have hK₁_compact : IsCompact K₁ := by
    -- Closure of a bounded set is compact in finite dimensions.
    simpa [K₁] using hQ₁_bounded.isCompact_closure
  have hK₂_compact : IsCompact K₂ := by
    -- The same compactness package applies to `K₂`.
    simpa [K₂] using hQ₂_bounded.isCompact_closure
  let ψ : E → ℝ := fun y ↦ (ξ[K₁] (x + y)).toReal + (ξ[K₂] (-y)).toReal
  obtain ⟨yStar, hyStar⟩ :=
    exists_isMinOn_supportFunction_sum_of_closedBall_subset_inter
      (K₁ := K₁) (K₂ := K₂) hK₁_compact hK₂_compact
      (c := c) (x := x) (ρ := r / 2) (by linarith) hclosedBall
  have hK₁_nonempty : K₁.Nonempty := hQ₁_nonempty.mono subset_closure
  have hK₂_nonempty : K₂.Nonempty := hQ₂_nonempty.mono subset_closure
  have hK₁_convex : Convex ℝ K₁ := by
    simpa [K₁] using hQ₁_convex.closure
  have hK₂_convex : Convex ℝ K₂ := by
    simpa [K₂] using hQ₂_convex.closure
  obtain ⟨g, hgK, hg₁, hg₂⟩ :=
    common_active_support_point_of_isMinOn_supportFunction_sum_real
      (K₁ := K₁) (K₂ := K₂)
      hK₁_compact hK₁_nonempty hK₂_compact hK₂_nonempty
      hK₁_convex hK₂_convex hyStar
  have hg_closure_inter : g ∈ closure (Q₁ ∩ Q₂) := by
    rcases hQ_int with ⟨z, hz_int⟩
    have hz₁ : z ∈ interior Q₁ := interior_mono Set.inter_subset_left hz_int
    have hz₂ : z ∈ interior Q₂ := interior_mono Set.inter_subset_right hz_int
    have hg₁_closure : g ∈ closure Q₁ := by
      simpa [K₁] using hgK.1
    have hg₂_closure : g ∈ closure Q₂ := by
      simpa [K₂] using hgK.2
    have hseg₁ : openSegment ℝ g z ⊆ Q₁ := by
      exact
        (hQ₁_convex.openSegment_closure_interior_subset_interior hg₁_closure hz₁).trans
          interior_subset
    have hseg₂ : openSegment ℝ g z ⊆ Q₂ := by
      exact
        (hQ₂_convex.openSegment_closure_interior_subset_interior hg₂_closure hz₂).trans
          interior_subset
    have hseg : openSegment ℝ g z ⊆ Q₁ ∩ Q₂ := by
      intro y hy
      exact ⟨hseg₁ hy, hseg₂ hy⟩
    refine closure_mono hseg ?_
    exact segment_subset_closure_openSegment (left_mem_segment ℝ g z)
  have hK₁_fin :=
    supportFunction_ne_top_ne_bot_of_isCompact hK₁_compact hK₁_nonempty (x + yStar)
  have hK₂_fin :=
    supportFunction_ne_top_ne_bot_of_isCompact hK₂_compact hK₂_nonempty (-yStar)
  have hsum_ne_top :
      ξ[K₁] (x + yStar) + ξ[K₂] (-yStar) ≠ ⊤ :=
    EReal.add_ne_top hK₁_fin.1 hK₂_fin.1
  have hsum_ne_bot :
      ξ[K₁] (x + yStar) + ξ[K₂] (-yStar) ≠ ⊥ :=
    (EReal.add_ne_bot_iff).2 ⟨hK₁_fin.2, hK₂_fin.2⟩
  have hvalue :
      ξ[K₁] (x + yStar) + ξ[K₂] (-yStar) = ((inner ℝ g x : ℝ) : EReal) := by
    -- The common active point rewrites the compact-closure objective to the exposed pairing.
    calc
      ξ[K₁] (x + yStar) + ξ[K₂] (-yStar)
          = ((((ξ[K₁] (x + yStar) + ξ[K₂] (-yStar)).toReal : ℝ)) : EReal) := by
              rw [EReal.coe_toReal hsum_ne_top hsum_ne_bot]
      _ = (((ξ[K₁] (x + yStar)).toReal + (ξ[K₂] (-yStar)).toReal : ℝ) : EReal) := by
            rw [EReal.toReal_add hK₁_fin.1 hK₁_fin.2 hK₂_fin.1 hK₂_fin.2]
      _ = ((inner ℝ g (x + yStar) + inner ℝ g (-yStar) : ℝ) : EReal) := by
            rw [hg₁, hg₂, EReal.coe_add]
      _ = ((inner ℝ g x : ℝ) : EReal) := by
            congr 1
            rw [inner_add_right, inner_neg_right]
            ring
  have hupper : ((inner ℝ g x : ℝ) : EReal) ≤ ξ[Q₁ ∩ Q₂] x := by
    have hupper_closure :
        ((inner ℝ g x : ℝ) : EReal) ≤ ξ[closure (Q₁ ∩ Q₂)] x :=
      le_supportFunction_of_mem hg_closure_inter
    rw [hξ_inter] at hupper_closure
    exact hupper_closure
  have hvalueφ : φ yStar = ((inner ℝ g x : ℝ) : EReal) := by
    dsimp [φ]
    rw [← hξK₁, ← hξK₂]
    exact hvalue
  have hstar_eq : φ yStar = ξ[Q₁ ∩ Q₂] x := by
    have hlower_star : ξ[Q₁ ∩ Q₂] x ≤ φ yStar := hlower yStar
    refine le_antisymm ?_ hlower_star
    rw [hvalueφ]
    exact hupper
  refine ⟨⟨yStar, hstar_eq⟩, ?_⟩
  intro z
  rintro ⟨y, rfl⟩
  calc
    ξ[Q₁ ∩ Q₂] x ≤ φ y := hlower y
    _ = ξ[Q₁] (x + y) + ξ[Q₂] (-y) := rfl

end
