/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_48

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

namespace Set

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

omit [Module ℝ E] in
/-- Helper for Proposition 6.49: the recession cone is closed under addition. -/
lemma recessionCone_add_mem {C : Set E} {x y : E} (hx : x ∈ rec C) (hy : y ∈ rec C) :
    x + y ∈ rec C := by
  -- Unfold both recession hypotheses into translate-inclusion statements.
  rw [mem_recessionCone_iff] at hx hy ⊢
  intro z hz
  rcases Set.mem_add.1 hz with ⟨w, hw, c, hc, rfl⟩
  have hw' : w = x + y := by
    simpa using hw
  subst hw'
  -- First translate by `y`, then by `x`.
  have hyc : y + c ∈ C := by
    exact hy (Set.add_mem_add (by simp) hc)
  have hxyc : x + (y + c) ∈ C := by
    exact hx (Set.add_mem_add (by simp) hyc)
  simpa [add_assoc] using hxyc

-- Proof sketch: if `x, y ∈ rec C`, then `({x} + C) ⊆ C` and `({y} + C) ⊆ C`; use convexity of `C`
-- to show every convex combination of `x` and `y` still translates `C` into itself.
/-- Proposition 6.49 (1): for a convex set `C`, the recession cone `rec C` is convex. -/
theorem recessionCone_convex {C : Set E} (hC_convex : Convex ℝ C) :
    Convex ℝ (rec C) := by
  -- Rewrite convexity of `rec C` into closure under affine combinations.
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  rw [mem_recessionCone_iff] at hx hy ⊢
  intro z hz
  rcases Set.mem_add.1 hz with ⟨w, hw, c, hc, rfl⟩
  have hw' : w = a • x + b • y := by
    simpa using hw
  subst hw'
  -- Apply the recession hypotheses to the common base point `c`.
  have hxz : x + c ∈ C := by
    exact hx (Set.add_mem_add (by simp) hc)
  have hyz : y + c ∈ C := by
    exact hy (Set.add_mem_add (by simp) hc)
  -- Convexity of `C` then keeps the same affine combination inside `C`.
  have hcombo : a • (x + c) + b • (y + c) ∈ C := by
    exact (convex_iff_add_mem.1 hC_convex) hxz hyz ha hb hab
  have hrewrite : a • (x + c) + b • (y + c) = a • x + b • y + c := by
    calc
      a • (x + c) + b • (y + c) = (a • x + a • c) + (b • y + b • c) := by
        rw [smul_add, smul_add]
      _ = (a • x + b • y) + (a • c + b • c) := by
        abel
      _ = (a • x + b • y) + (a + b) • c := by
        rw [← add_smul]
      _ = (a • x + b • y) + c := by
        rw [hab, one_smul]
      _ = a • x + b • y + c := by
        rw [add_assoc]
  exact hrewrite ▸ hcombo

-- Proof sketch: use convexity of `C` to obtain closure of `rec C` under positive dilations by
-- interpolating between `c` and `x + c` when the scalar is in `(0, 1]`, then extend to all
-- positive scalars by repeated translation.
/-- Proposition 6.49 (2): for a convex set `C`, the recession cone `rec C` is a cone. -/
theorem recessionCone_isCone {C : Set E} (hC_convex : Convex ℝ C) :
    IsCone (rec C) := by
  have h0 : (0 : E) ∈ rec C := by
    -- The zero translation leaves every point of `C` unchanged.
    rw [mem_recessionCone_iff]
    intro z hz
    simpa using hz
  have hAdd : rec C + rec C ⊆ rec C := by
    intro z hz
    rcases Set.mem_add.1 hz with ⟨x, hx, y, hy, rfl⟩
    -- Additive closure is the structural part needed by Proposition 6.3.
    exact recessionCone_add_mem hx hy
  -- Proposition 6.3 upgrades convexity, zero membership, and additive closure to the cone law.
  exact (Convex.isCone_iff_add_subset (recessionCone_convex hC_convex) h0).2 hAdd

omit [Module ℝ E] in
-- Proof sketch: the zero translation fixes every point of `C`, so `({0} : Set E) + C = C`.
/-- Proposition 6.49 (3): the zero vector belongs to the recession cone of every set. -/
theorem zero_mem_recessionCone (C : Set E) :
    (0 : E) ∈ rec C := by
  -- Unfold the defining translate condition and simplify.
  rw [mem_recessionCone_iff]
  intro z hz
  simpa using hz

end

/-- Helper for Proposition 6.49: local fallback for the source-facing polar cone while
`Definition_6_22` is unavailable. -/
private def sourcePolarCone {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
    (C : Set 𝓗) : Set 𝓗 :=
  {u | sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C) ≤ 0}

local postfix:100 "ᵒ⊖" => Set.sourcePolarCone

/-- Helper for Proposition 6.49: membership in the local fallback polar cone is the defining
support inequality. -/
private theorem mem_sourcePolarCone_iff {𝓗 : Type u} [NormedAddCommGroup 𝓗]
    [InnerProductSpace ℝ 𝓗] {C : Set 𝓗} {u : 𝓗} :
    u ∈ Cᵒ⊖ ↔ sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C) ≤ 0 := by
  rfl

/-- Helper for Proposition 6.49: the local fallback polar cone is characterized by pointwise
nonpositive inner products on `C`. -/
private theorem mem_sourcePolarCone_iff_forall_inner_nonpos {𝓗 : Type u}
    [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] {C : Set 𝓗} {u : 𝓗} :
    u ∈ Cᵒ⊖ ↔ ∀ x ∈ C, ⟪x, u⟫_ℝ ≤ 0 := by
  rw [mem_sourcePolarCone_iff, sSup_le_iff]
  constructor
  · intro hu x hx
    have hxu : (⟪x, u⟫_ℝ : EReal) ≤ (0 : EReal) :=
      hu _ (Set.mem_image_of_mem _ hx)
    exact_mod_cast hxu
  · intro hu a ha
    rcases ha with ⟨x, hx, rfl⟩
    have hxu : (⟪x, u⟫_ℝ : EReal) ≤ (0 : EReal) := by
      exact_mod_cast hu x hx
    simpa using hxu

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Helper for Proposition 6.49: a pointwise real upper bound on `⟪x, u⟫` controls the support
value `innerSupremumOn C u`. -/
private lemma innerSupremumOn_le_of_forall_inner_le {C : Set 𝓗} {u : 𝓗} {a : ℝ}
    (hbound : ∀ x ∈ C, ⟪x, u⟫_ℝ ≤ a) :
    innerSupremumOn C u ≤ (a : EReal) := by
  -- Rewrite the support value as a supremum and show that `a` is an upper bound.
  rw [innerSupremumOn_eq_sSup_image]
  refine (isLUB_sSup _).2 ?_
  rintro _ ⟨x, hx, rfl⟩
  exact show ((⟪x, u⟫_ℝ : EReal) ≤ (a : EReal)) by
    exact_mod_cast hbound x hx

/-- Helper for Proposition 6.49: barrier-cone membership is equivalent to the existence of a real
upper bound for the corresponding inner products on `C`. -/
theorem mem_barrierCone_iff_exists_real_upper_bound {C : Set 𝓗} {u : 𝓗} :
    u ∈ bar C ↔ ∃ a : ℝ, ∀ x ∈ C, ⟪x, u⟫_ℝ ≤ a := by
  constructor
  · intro hu
    rw [mem_barrierCone_iff] at hu
    by_cases hC_nonempty : C.Nonempty
    · rcases hC_nonempty with ⟨x₀, hx₀⟩
      have hx₀_le : (⟪x₀, u⟫_ℝ : EReal) ≤ innerSupremumOn C u := by
        rw [innerSupremumOn_eq_sSup_image]
        exact (isLUB_sSup _).1 (Set.mem_image_of_mem _ hx₀)
      have hσ_bot_ne : innerSupremumOn C u ≠ ⊥ := by
        have hbot_lt : (⊥ : EReal) < innerSupremumOn C u := by
          exact lt_of_lt_of_le (EReal.bot_lt_coe _) hx₀_le
        exact ne_of_gt hbot_lt
      have hσ_top_ne : innerSupremumOn C u ≠ ⊤ := ne_of_lt hu
      refine ⟨(innerSupremumOn C u).toReal, ?_⟩
      intro x hx
      have hx_le : (⟪x, u⟫_ℝ : EReal) ≤ innerSupremumOn C u := by
        rw [innerSupremumOn_eq_sSup_image]
        exact (isLUB_sSup _).1 (Set.mem_image_of_mem _ hx)
      have hσ_real : ((innerSupremumOn C u).toReal : EReal) = innerSupremumOn C u := by
        exact EReal.coe_toReal hσ_top_ne hσ_bot_ne
      have hx_le' : (⟪x, u⟫_ℝ : EReal) ≤ (((innerSupremumOn C u).toReal : ℝ) : EReal) := by
        simpa [hσ_real] using hx_le
      exact_mod_cast hx_le'
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hC_nonempty ⟨x, hx⟩).elim
  · rintro ⟨a, ha⟩
    rw [mem_barrierCone_iff]
    have hsup : innerSupremumOn C u ≤ (a : EReal) :=
      innerSupremumOn_le_of_forall_inner_le ha
    -- A finite real upper bound proves that the support value is strictly below `⊤`.
    exact lt_of_le_of_lt hsup (EReal.coe_lt_top a)

/-- Helper for Proposition 6.49: an arithmetic ray with positive directional growth forces
non-membership in the barrier cone. -/
lemma not_mem_barrierCone_of_nat_ray_inner_pos {C : Set 𝓗} {y d u : 𝓗}
    (hray : ∀ n : ℕ, y + (n : ℝ) • d ∈ C) (hpos : 0 < ⟪d, u⟫_ℝ) :
    u ∉ bar C := by
  intro hu
  rcases mem_barrierCone_iff_exists_real_upper_bound.1 hu with ⟨a, ha⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ((a - ⟪y, u⟫_ℝ) / ⟪d, u⟫_ℝ)
  have hupper : ⟪y + (n : ℝ) • d, u⟫_ℝ ≤ a := ha _ (hray n)
  have hmul : a - ⟪y, u⟫_ℝ < (n : ℝ) * ⟪d, u⟫_ℝ := by
    exact (div_lt_iff₀ hpos).mp hn
  have hstrict : a < ⟪y + (n : ℝ) • d, u⟫_ℝ := by
    rw [inner_add_left, real_inner_smul_left]
    nlinarith
  linarith

/-- Helper for Proposition 6.49: translating by a singleton does not change the barrier cone. -/
theorem barrierCone_sub_singleton_eq {C : Set 𝓗} (p : 𝓗) :
    bar (C - ({p} : Set 𝓗)) = bar C := by
  ext u
  constructor
  · intro hu
    rw [mem_barrierCone_iff_exists_real_upper_bound] at hu ⊢
    rcases hu with ⟨a, ha⟩
    refine ⟨a + ⟪p, u⟫_ℝ, ?_⟩
    intro y hy
    have hy_sub : y - p ∈ C - ({p} : Set 𝓗) := by
      exact Set.mem_sub.2 ⟨y, hy, p, by simp, rfl⟩
    have hbound := ha (y - p) hy_sub
    rw [inner_sub_left] at hbound
    linarith
  · intro hu
    rw [mem_barrierCone_iff_exists_real_upper_bound] at hu ⊢
    rcases hu with ⟨a, ha⟩
    refine ⟨a - ⟪p, u⟫_ℝ, ?_⟩
    intro v hv
    rcases Set.mem_sub.1 hv with ⟨y, hy, w, hw, rfl⟩
    have hw' : w = p := by
      simpa using hw
    subst hw'
    have hbound := ha y hy
    rw [inner_sub_left]
    linarith

-- Proof sketch: if `u` and `v` have finite support values on `C`, then any convex combination of
-- their inner products is bounded above by the corresponding convex combination of those finite
-- bounds.
/-- Proposition 6.49 (4): the barrier cone `bar C` is convex. -/
theorem barrierCone_convex (C : Set 𝓗) :
    Convex ℝ (bar C) := by
  -- Rewrite convexity into the affine-combination form on barrier-cone bounds.
  rw [convex_iff_add_mem]
  intro u hu v hv a b ha hb hab
  rw [mem_barrierCone_iff_exists_real_upper_bound] at hu hv ⊢
  rcases hu with ⟨α, hα⟩
  rcases hv with ⟨β, hβ⟩
  refine ⟨a * α + b * β, ?_⟩
  intro x hx
  -- The inner product distributes over the affine combination, and the coefficients are nonnegative.
  calc
    ⟪x, a • u + b • v⟫_ℝ = a * ⟪x, u⟫_ℝ + b * ⟪x, v⟫_ℝ := by
      rw [inner_add_right, inner_smul_right, inner_smul_right]
    _ ≤ a * α + b * β := by
      gcongr
      exact hα x hx
      exact hβ x hx

-- Proof sketch: positive dilations of a direction rescale the support value by the same positive
-- scalar, so finiteness of `innerSupremumOn C u` is preserved.
/-- Proposition 6.49 (5): the barrier cone `bar C` is a cone. -/
theorem barrierCone_isCone (C : Set 𝓗) :
    IsCone (bar C) := by
  have h0 : (0 : 𝓗) ∈ bar C := by
    -- The zero functional is bounded above by the real number `0`.
    rw [mem_barrierCone_iff_exists_real_upper_bound]
    refine ⟨0, ?_⟩
    intro x hx
    simp
  have hAdd : bar C + bar C ⊆ bar C := by
    intro w hw
    rcases Set.mem_add.1 hw with ⟨u, hu, v, hv, rfl⟩
    rw [mem_barrierCone_iff_exists_real_upper_bound] at hu hv ⊢
    rcases hu with ⟨α, hα⟩
    rcases hv with ⟨β, hβ⟩
    refine ⟨α + β, ?_⟩
    intro x hx
    -- Add the two pointwise upper bounds.
    calc
      ⟪x, u + v⟫_ℝ = ⟪x, u⟫_ℝ + ⟪x, v⟫_ℝ := by
        rw [inner_add_right]
      _ ≤ α + β := by
        linarith [hα x hx, hβ x hx]
  -- Proposition 6.3 again upgrades convexity plus additive closure to the cone law.
  exact (Convex.isCone_iff_add_subset (barrierCone_convex C) h0).2 hAdd

-- Proof sketch: if `u ∈ Cᵒ⊖`, then every inner product `⟪x, u⟫` with `x ∈ C` is nonpositive, so
-- `innerSupremumOn C u ≤ 0 < ⊤`, which is exactly membership in `bar C`.
/-- Proposition 6.49 (6): the polar cone of `C` is contained in the barrier cone of `C`. -/
theorem polarCone_subset_barrierCone (C : Set 𝓗) :
    Cᵒ⊖ ⊆ bar C := by
  intro u hu
  rw [mem_sourcePolarCone_iff_forall_inner_nonpos] at hu
  rw [mem_barrierCone_iff_exists_real_upper_bound]
  -- The polar inequality gives the uniform upper bound `0`.
  exact ⟨0, fun x hx ↦ hu x hx⟩

-- Proof sketch: a bounded set has uniformly bounded inner products in every fixed direction by
-- Cauchy-Schwarz, so every direction belongs to the barrier cone.
/-- Proposition 6.49 (7): if `C` is bounded, then its barrier cone is the whole space. -/
theorem barrierCone_eq_univ_of_bounded {C : Set 𝓗} (hC_bounded : Bornology.IsBounded C) :
    bar C = univ := by
  refine Set.eq_univ_iff_forall.mpr ?_
  intro u
  rw [mem_barrierCone_iff_exists_real_upper_bound]
  rcases isBounded_iff_forall_norm_le.mp hC_bounded with ⟨R, hR⟩
  refine ⟨R * ‖u‖, ?_⟩
  intro x hx
  -- Cauchy-Schwarz turns the norm bound on `C` into a support bound in direction `u`.
  calc
    ⟪x, u⟫_ℝ ≤ ‖x‖ * ‖u‖ := real_inner_le_norm x u
    _ ≤ R * ‖u‖ := by
      gcongr
      exact hR x hx

-- Proof sketch: if `C` is a cone and some `x ∈ C` satisfies `0 < ⟪x, u⟫`, then positive dilations
-- of `x` force `innerSupremumOn C u = ⊤`; conversely, every vector in `Cᵒ⊖` has support value at
-- most `0`, hence lies in `bar C`.
/-- Proposition 6.49 (8): if `C` is a cone, then its barrier cone equals its polar cone. -/
theorem barrierCone_eq_polarCone_of_isCone {C : Set 𝓗} (hC_cone : IsCone C) :
    bar C = Cᵒ⊖ := by
  ext u
  constructor
  · intro hu
    rw [mem_sourcePolarCone_iff_forall_inner_nonpos]
    rw [Set.isCone_iff_nonneg_smul_mem] at hC_cone
    intro x hx
    by_contra hxu
    have hpos : 0 < ⟪x, u⟫_ℝ := lt_of_not_ge hxu
    have hray : ∀ n : ℕ, x + (n : ℝ) • x ∈ C := by
      intro n
      have hmul : (((n + 1 : ℕ) : ℝ)) • x ∈ C := by
        rw [hC_cone]
        exact Set.mem_smul.mpr
          ⟨((n + 1 : ℕ) : ℝ), by
            simpa using (show (0 : ℝ) < ((n + 1 : ℕ) : ℝ) by
              exact_mod_cast Nat.succ_pos n), x, hx, rfl⟩
      simpa [Nat.cast_add, add_smul, one_smul, add_comm, add_left_comm, add_assoc] using hmul
    exact not_mem_barrierCone_of_nat_ray_inner_pos hray hpos hu
  · intro hu
    exact polarCone_subset_barrierCone C hu

end

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

-- Proof sketch: for `x ∈ rec C`, every `u ∈ bar C` satisfies `⟪x, u⟫ ≤ 0` because translating `C`
-- by `x` does not increase its support value, giving `rec C ⊆ (bar C)ᵒ⊖`. For the converse, use
-- the projection characterization of closed convex sets to show that if `x ∈ (bar C)ᵒ⊖`, then
-- every translate `x + y` with `y ∈ C` projects back to itself and therefore lies in `C`.
/-- Proposition 6.49 (9): for a nonempty closed convex set `C`, the polar cone of the barrier cone
is the recession cone of `C`. -/
theorem polarCone_barrierCone_eq_recessionCone_of_nonempty_isClosed_convex {C : Set 𝓗}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    (bar C)ᵒ⊖ = rec C := by
  ext x
  constructor
  · intro hx
    rw [mem_recessionCone_iff]
    intro y hy
    rcases Set.mem_add.1 hy with ⟨w, hw, z, hz, rfl⟩
    have hw' : w = x := by
      simpa using hw
    subst w
    let p :=
      projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
        (x + z)
    have hp : p ∈ C := by
      exact
        projectionPoint_mem C
          (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) (x + z)
    have hproj :
        p ∈ C ∧ ∀ v ∈ C, ⟪v - p, x + z - p⟫_ℝ ≤ 0 := by
      -- The Chapter 3 characterization supplies the variational inequality at the projection.
      exact
        (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex).mp rfl
    have hres_sup : innerSupremumOn (C - ({p} : Set 𝓗)) (x + z - p) ≤ 0 := by
      -- The projection inequality bounds every translate `z - p` with `z ∈ C`.
      refine innerSupremumOn_le_of_forall_inner_le ?_
      intro v hv
      rcases Set.mem_sub.1 hv with ⟨v', hv', w, hw, rfl⟩
      have hw' : w = p := by
        simpa using hw
      subst w
      simpa using hproj.2 v' hv'
    have hres_polar : x + z - p ∈ (C - ({p} : Set 𝓗))ᵒ⊖ := by
      rw [mem_sourcePolarCone_iff]
      simpa [innerSupremumOn_eq_sSup_image] using hres_sup
    have hres_bar_sub : x + z - p ∈ bar (C - ({p} : Set 𝓗)) := by
      exact polarCone_subset_barrierCone (C - ({p} : Set 𝓗)) hres_polar
    have hres_bar : x + z - p ∈ bar C := by
      rw [barrierCone_sub_singleton_eq (C := C) p] at hres_bar_sub
      exact hres_bar_sub
    rw [mem_sourcePolarCone_iff_forall_inner_nonpos] at hx
    have hx_nonpos : ⟪x + z - p, x⟫_ℝ ≤ 0 := hx (x + z - p) hres_bar
    have hy_nonpos : ⟪x + z - p, z - p⟫_ℝ ≤ 0 := by
      simpa [real_inner_comm] using hproj.2 z hz
    have hnorm_sq_nonpos : ‖x + z - p‖ ^ 2 ≤ 0 := by
      -- Split the residual against `x + (y - p)` and use the two nonpositive terms.
      calc
        ‖x + z - p‖ ^ 2 = ⟪x + z - p, x + z - p⟫_ℝ := by
          rw [real_inner_self_eq_norm_sq]
        _ = ⟪x + z - p, x⟫_ℝ + ⟪x + z - p, z - p⟫_ℝ := by
          rw [show x + z - p = x + (z - p) by abel, inner_add_right]
        _ ≤ 0 := by
          linarith
    have hnorm_sq_zero : ‖x + z - p‖ ^ 2 = 0 := by
      refine le_antisymm hnorm_sq_nonpos ?_
      positivity
    have hres_zero : x + z - p = 0 := by
      apply norm_eq_zero.mp
      nlinarith [hnorm_sq_zero]
    have hxy_eq : x + z = p := by
      exact sub_eq_zero.mp hres_zero
    simpa [hxy_eq] using hp
  · intro hx
    rw [mem_sourcePolarCone_iff_forall_inner_nonpos]
    rw [mem_recessionCone_iff] at hx
    rcases hC_nonempty with ⟨y₀, hy₀⟩
    have hrec_cone : IsCone (rec C) := recessionCone_isCone hC_convex
    rw [Set.isCone_iff_nonneg_smul_mem] at hrec_cone
    intro u hu
    by_contra hxu
    have hpos : 0 < ⟪x, u⟫_ℝ := by
      simpa [real_inner_comm] using (lt_of_not_ge hxu)
    have hray : ∀ n : ℕ, y₀ + (n : ℝ) • x ∈ C := by
      intro n
      cases n with
      | zero =>
          simpa using hy₀
      | succ n =>
          have hnx : (((n + 1 : ℕ) : ℝ)) • x ∈ rec C := by
            rw [hrec_cone]
            exact Set.mem_smul.mpr
              ⟨((n + 1 : ℕ) : ℝ), by
                simpa using (show (0 : ℝ) < ((n + 1 : ℕ) : ℝ) by
                  exact_mod_cast Nat.succ_pos n), x, hx, rfl⟩
          have hnx_translate :=
            (mem_recessionCone_iff.1 hnx)
              (Set.mem_add.2 ⟨(((n + 1 : ℕ) : ℝ)) • x, by simp, y₀, hy₀, rfl⟩)
          simpa [Nat.cast_add, add_smul, one_smul, add_comm, add_left_comm, add_assoc] using
            hnx_translate
    exact not_mem_barrierCone_of_nat_ray_inner_pos hray hpos hu

end

end Set
