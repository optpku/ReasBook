/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Corrollary_8_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Definition_10_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Proposition_10_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Pointwise

namespace ERealFunction

section RealVectorSpace

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

omit [AddCommGroup H] [Module ℝ H] in
private theorem exists_real_ge_of_mem_dom (f : H → EReal) {x : H} (hx : x ∈ dom f) :
    ∃ ξ : ℝ, f x ≤ (ξ : EReal) := by
  rw [mem_dom_iff] at hx
  rcases EReal.lt_iff_exists_real_btwn.mp hx with ⟨ξ, hξ, _⟩
  exact ⟨ξ, le_of_lt hξ⟩

omit [AddCommGroup H] [Module ℝ H] in
private theorem value_eq_top_of_not_mem_dom (f : H → EReal) {x : H} (hx : x ∉ dom f) :
    f x = ⊤ := by
  by_contra htop
  exact hx <| (mem_dom_iff f x).2 <| lt_of_le_of_ne le_top htop

omit [Module ℝ H] in
private theorem add_subset_epigraph_of_subadditive {f : H → EReal} (hf : Subadditive f) :
    epigraph f + epigraph f ⊆ epigraph f := by
  rintro _ ⟨⟨x, ξ⟩, hx, ⟨y, η⟩, hy, rfl⟩
  rw [mem_epigraph_iff] at hx hy ⊢
  have hxd : x ∈ dom f := by
    rw [mem_dom_iff]
    exact lt_of_le_of_lt hx (EReal.coe_lt_top ξ)
  have hyd : y ∈ dom f := by
    rw [mem_dom_iff]
    exact lt_of_le_of_lt hy (EReal.coe_lt_top η)
  calc
    f (x + y) ≤ f x + f y := hf.map_add_le hxd hyd
    _ ≤ (ξ : EReal) + (η : EReal) := add_le_add hx hy

omit [Module ℝ H] in
private theorem value_eq_bot_of_add_subset_epigraph {f : H → EReal}
    (hf : epigraph f + epigraph f ⊆ epigraph f) {x y : H} (hx : f x = ⊥) (hy : y ∈ dom f) :
    f (x + y) = ⊥ := by
  rcases exists_real_ge_of_mem_dom f hy with ⟨η, hη⟩
  refine (EReal.eq_bot_iff_forall_lt _).2 ?_
  intro r
  let ξ : ℝ := r - η - 1
  have hx_epi : (x, ξ) ∈ epigraph f := by
    rw [mem_epigraph_iff, hx]
    simp [ξ]
  have hy_epi : (y, η) ∈ epigraph f := by
    simpa [mem_epigraph_iff] using hη
  have hxy_epi : (x + y, ξ + η) ∈ epigraph f := by
    exact hf <| Set.mem_add.2 ⟨(x, ξ), hx_epi, (y, η), hy_epi, by simp [ξ]⟩
  rw [mem_epigraph_iff] at hxy_epi
  have hlt : ((ξ + η : ℝ) : EReal) < (r : EReal) := by
    rw [show ξ + η = r - 1 by
      dsimp [ξ]
      ring]
    exact EReal.coe_lt_coe_iff.mpr (sub_lt_self _ zero_lt_one)
  exact lt_of_le_of_lt hxy_epi hlt

omit [Module ℝ H] in
private theorem subadditive_of_add_subset_epigraph {f : H → EReal}
    (hf : epigraph f + epigraph f ⊆ epigraph f) :
    Subadditive f := by
  intro x y hx hy
  by_cases hfx : f x = ⊥
  · have hxy_bot : f (x + y) = ⊥ :=
      value_eq_bot_of_add_subset_epigraph hf hfx hy
    simp [hxy_bot, hfx]
  · by_cases hfy : f y = ⊥
    · have hyx_bot : f (y + x) = ⊥ :=
        value_eq_bot_of_add_subset_epigraph hf hfy hx
      have hxy_bot : f (x + y) = ⊥ := by
        simpa [add_comm] using hyx_bot
      simp [hxy_bot, hfy]
    · have hxtop : f x ≠ ⊤ := ne_of_lt ((mem_dom_iff f x).mp hx)
      have hytop : f y ≠ ⊤ := ne_of_lt ((mem_dom_iff f y).mp hy)
      have hx_epi : (x, (f x).toReal) ∈ epigraph f := by
        simp [mem_epigraph_iff, EReal.coe_toReal hxtop hfx]
      have hy_epi : (y, (f y).toReal) ∈ epigraph f := by
        simp [mem_epigraph_iff, EReal.coe_toReal hytop hfy]
      have hxy_epi : (x + y, (f x).toReal + (f y).toReal) ∈ epigraph f := by
        exact hf <| Set.mem_add.2 ⟨(x, (f x).toReal), hx_epi, (y, (f y).toReal), hy_epi, by simp⟩
      rw [mem_epigraph_iff] at hxy_epi
      calc
        f (x + y) ≤ (((f x).toReal + (f y).toReal : ℝ) : EReal) := hxy_epi
        _ = f x + f y := by
          rw [EReal.coe_add, EReal.coe_toReal hxtop hfx, EReal.coe_toReal hytop hfy]

private theorem smul_mem_of_isCone {C : Set H} (hC_cone : IsCone C) {x : H} (hx : x ∈ C)
    {a : ℝ} (ha : 0 < a) :
    a • x ∈ C := by
  rw [isCone_iff] at hC_cone
  exact hC_cone.symm ▸ Set.mem_smul.mpr ⟨a, ha, x, hx, rfl⟩

private theorem convex_iff_add_subset_of_isCone {C : Set H} (hC_cone : IsCone C) :
    Convex ℝ C ↔ C + C ⊆ C := by
  constructor
  · intro hC_convex z hz
    rcases Set.mem_add.1 hz with ⟨x, hx, y, hy, rfl⟩
    have hmid : ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ∈ C := by
      exact (convex_iff_add_mem.1 hC_convex) hx hy (by positivity) (by positivity) (by norm_num)
    have hsum : (2 : ℝ) • (((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)) ∈ C := by
      exact smul_mem_of_isCone hC_cone hmid (by positivity)
    simpa [smul_add, smul_smul] using hsum
  · intro hAdd
    rw [convex_iff_add_mem]
    intro x hx y hy a b ha hb hab
    by_cases ha_zero : a = 0
    · subst ha_zero
      have hb_one : b = 1 := by linarith
      subst hb_one
      simpa using hy
    by_cases hb_zero : b = 0
    · subst hb_zero
      have ha_one : a = 1 := by linarith
      subst ha_one
      simpa using hx
    have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha_zero)
    have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb_zero)
    exact hAdd <| Set.add_mem_add
      (smul_mem_of_isCone hC_cone hx ha_pos)
      (smul_mem_of_isCone hC_cone hy hb_pos)

-- Proof sketch: positive homogeneity makes the epigraph a cone and the domain a cone. For the
-- forward direction, combine subadditivity with positive homogeneity to obtain the Jensen
-- inequality on `dom f`, then invoke Proposition 8.4. For the reverse direction, convexity of the
-- conic epigraph is equivalent to additive closure by Proposition 6.3, and additive closure of the
-- epigraph is exactly subadditivity.
/-- Under a fixed positive-homogeneity hypothesis, subadditivity is equivalent to convexity of the
epigraph. This is the core epigraph-level owner of Proposition 10.3. -/
theorem subadditive_iff_convex_epigraph_of_positivelyHomogeneous (f : H → EReal)
    (hf : PositivelyHomogeneous f) :
    Subadditive f ↔ Convex ℝ (epigraph f) := by
  constructor
  · intro hsub
    have hdom_cone : IsCone (dom f) :=
      isCone_dom_of_isCone_epigraph
        ((positivelyHomogeneous_iff_isCone_epigraph f).1 hf)
    refine (convex_epigraph_iff_jensen_on_dom f).2 ?_
    intro x y hx hy a ha ha_lt_one
    have hax : a • x ∈ dom f := by
      exact smul_mem_of_isCone hdom_cone hx ha
    have hay : (1 - a) • y ∈ dom f := by
      exact smul_mem_of_isCone hdom_cone hy (sub_pos.mpr ha_lt_one)
    calc
      f (a • x + (1 - a) • y) ≤ f (a • x) + f ((1 - a) • y) := hsub.map_add_le hax hay
      _ = (a : EReal) * f x + (((1 - a : ℝ) : EReal) * f y) := by
        rw [hf.map_smul_of_pos ha x, hf.map_smul_of_pos (sub_pos.mpr ha_lt_one) y]
        simp [EReal.real_smul_def]
  · intro hconv
    have hcone_epi : IsCone (epigraph f) :=
      (positivelyHomogeneous_iff_isCone_epigraph f).1 hf
    exact subadditive_of_add_subset_epigraph
      ((convex_iff_add_subset_of_isCone hcone_epi).1 hconv)

/-- For `]-∞,+∞]`-valued functions, Jensen convexity on the closed segment implies convexity of
the real-height epigraph. -/
theorem convex_epigraph_of_isConvex (f : H → Set.Ioi (⊥ : EReal))
    (hf : IsConvex fun x : H ↦ (f x : EReal)) :
    Convex ℝ (epigraph fun x : H ↦ (f x : EReal)) := by
  refine (convex_epigraph_iff_closedSegment_jensen (fun x : H ↦ (f x : EReal))).2 ?_
  intro x y a ha _ _
  exact hf ha.1 ha.2

/-- For `]-∞,+∞]`-valued functions, convexity of the real-height epigraph upgrades to the
source-facing Jensen convexity predicate. -/
theorem isConvex_of_convex_epigraph (f : H → Set.Ioi (⊥ : EReal))
    (hf : Convex ℝ (epigraph fun x : H ↦ (f x : EReal))) :
    IsConvex fun x : H ↦ (f x : EReal) := by
  intro x y a ha0 ha1
  have hcoef_eq : (1 - (a : EReal)) = ((1 - a : ℝ) : EReal) := by
    norm_num
  change (f (a • x + (1 - a) • y) : EReal) ≤
    (a : EReal) * (f x : EReal) + (1 - (a : EReal)) * (f y : EReal)
  by_cases ha_zero : a = 0
  · subst ha_zero
    simp
  by_cases ha_one : a = 1
  · subst ha_one
    rw [hcoef_eq]
    simp
  have ha_pos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha_zero)
  have ha_lt_one : a < 1 := lt_of_le_of_ne ha1 ha_one
  by_cases hx : x ∈ dom (fun z : H ↦ (f z : EReal))
  · by_cases hy : y ∈ dom (fun z : H ↦ (f z : EReal))
    · exact (convex_epigraph_iff_jensen_on_dom (fun z : H ↦ (f z : EReal))).1
        hf hx hy ha_pos ha_lt_one |>.trans_eq (by rw [hcoef_eq])
    · have hy_top : (f y : EReal) =
        ⊤ := value_eq_top_of_not_mem_dom (fun z : H ↦ (f z : EReal)) hy
      have hx_term_ne_bot : (a : EReal) * (f x : EReal) ≠ ⊥ := by
        rw [EReal.mul_ne_bot]
        refine ⟨Or.inl (EReal.coe_ne_bot a), Or.inr (f x).property.ne',
          Or.inl (EReal.coe_ne_top a), Or.inl (EReal.coe_nonneg.mpr ha0)⟩
      rw [hcoef_eq, hy_top, EReal.mul_top_of_pos (EReal.coe_pos.mpr (sub_pos.mpr ha_lt_one))]
      exact by
        simp [EReal.add_top_of_ne_bot hx_term_ne_bot]
  · have hx_top : (f x : EReal) =
      ⊤ := value_eq_top_of_not_mem_dom (fun z : H ↦ (f z : EReal)) hx
    have hy_term_ne_bot : (((1 - a : ℝ) : EReal) * (f y : EReal)) ≠ ⊥ := by
      rw [EReal.mul_ne_bot]
      refine ⟨Or.inl (EReal.coe_ne_bot (1 - a)), Or.inr (f y).property.ne',
        Or.inl (EReal.coe_ne_top (1 - a)),
        Or.inl (EReal.coe_nonneg.mpr (sub_nonneg.mpr ha1))⟩
    have hrhs_top :
        (a : EReal) * (f x : EReal) + (1 - (a : EReal)) * (f y : EReal) = ⊤ := by
      rw [hx_top, hcoef_eq, EReal.mul_top_of_pos (EReal.coe_pos.mpr ha_pos)]
      exact EReal.top_add_of_ne_bot hy_term_ne_bot
    exact by
      simp [hrhs_top]

/-- Under a fixed positive-homogeneity hypothesis, a `]-∞,+∞]`-valued function is subadditive if
and only if it is Jensen convex. -/
theorem subadditive_iff_isConvex_of_positivelyHomogeneous
    (f : H → Set.Ioi (⊥ : EReal))
    (hf : PositivelyHomogeneous fun x : H ↦ (f x : EReal)) :
    Subadditive (fun x : H ↦ (f x : EReal)) ↔ IsConvex (fun x : H ↦ (f x : EReal)) := by
  rw [subadditive_iff_convex_epigraph_of_positivelyHomogeneous
    (fun x : H ↦ (f x : EReal)) hf]
  exact ⟨isConvex_of_convex_epigraph f, convex_epigraph_of_isConvex f⟩

/-- Under a fixed positive-homogeneity hypothesis, a `]-∞,+∞]`-valued function is sublinear if
and only if it has convex epigraph. -/
theorem sublinear_iff_convex_epigraph_of_positivelyHomogeneous (f : H → EReal)
    (hf : PositivelyHomogeneous f) :
    Sublinear f ↔ Convex ℝ (epigraph f) := by
  rw [Sublinear]
  constructor
  · intro hsublinear
    exact (subadditive_iff_convex_epigraph_of_positivelyHomogeneous f
      hsublinear.1).1 hsublinear.2
  · intro hconv
    exact ⟨hf, (subadditive_iff_convex_epigraph_of_positivelyHomogeneous f hf).2 hconv⟩

/-- Proposition 10.3: a positively homogeneous `]-∞,+∞]`-valued function on a real vector space
is sublinear if and only if it is Jensen convex. -/
theorem sublinear_iff_isConvex_of_positivelyHomogeneous
    (f : H → Set.Ioi (⊥ : EReal))
    (hf : PositivelyHomogeneous fun x : H ↦ (f x : EReal)) :
    Sublinear (fun x : H ↦ (f x : EReal)) ↔ IsConvex (fun x : H ↦ (f x : EReal)) := by
  rw [sublinear_iff_convex_epigraph_of_positivelyHomogeneous
    (fun x : H ↦ (f x : EReal)) hf]
  exact ⟨isConvex_of_convex_epigraph f, convex_epigraph_of_isConvex f⟩

end RealVectorSpace

end ERealFunction
