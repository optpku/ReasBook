/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Topology

namespace ERealFunction

/-- Helper for Corollary 9.15: the effective domain of a `Γ₀(ℝ)` function is a convex subset of
`ℝ`, hence an interval. -/
private lemma convex_effectiveDomain_of_mem_gammaZero
    {f : ℝ → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(ℝ)) :
    Convex ℝ (effectiveDomain f) := by
  -- Convert the defining Jensen inequality into finiteness of all convex combinations.
  refine (convex_iff_forall_pos).2 ?_
  intro x hx y hy a b ha hb hab
  rw [mem_effectiveDomain_iff]
  have hb_eq : b = 1 - a := by
    linarith
  have hineq := hf.2.ineq hx hy ha (by linarith)
  have hxtop : (f x : EReal) ≠ ⊤ := ne_of_lt hx
  have hytop : (f y : EReal) ≠ ⊤ := ne_of_lt hy
  have hxbot : (f x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hybot : (f y : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hfx : (f x : EReal) = (((f x : EReal).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal hxtop hxbot).symm
  have hfy : (f y : EReal) = (((f y : EReal).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal hytop hybot).symm
  calc
    (f (a • x + b • y) : EReal)
        ≤ (a : EReal) * (f x : EReal) + ((1 - a : ℝ) : EReal) * (f y : EReal) := by
          simpa [hb_eq] using hineq
    _ = ((a * (f x : EReal).toReal + (1 - a) * (f y : EReal).toReal : ℝ) : EReal) := by
          rw [hfx, hfy, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
          simp
    _ < ⊤ := EReal.coe_lt_top _

/-- Helper for Corollary 9.15: on the effective domain, the real-valued representative satisfies
the same two-point convexity inequality. -/
private lemma toReal_weighted_average_le
    {f : ℝ → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(ℝ))
    {x y : ℝ} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (f (a • x + b • y) : EReal).toReal ≤
      a * (f x : EReal).toReal + b * (f y : EReal).toReal := by
  -- Rewrite the EReal-valued Jensen inequality into a real-valued one via `toReal`.
  have hb_eq : b = 1 - a := by
    linarith
  have hineq' :
      (f (a • x + b • y) : EReal) ≤
        ((a * (f x : EReal).toReal + b * (f y : EReal).toReal : ℝ) : EReal) := by
    have hineq := hf.2.ineq hx hy ha (by linarith)
    have hxtop : (f x : EReal) ≠ ⊤ := ne_of_lt hx
    have hytop : (f y : EReal) ≠ ⊤ := ne_of_lt hy
    have hxbot : (f x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hybot : (f y : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
    have hfx : (f x : EReal) = (((f x : EReal).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal hxtop hxbot).symm
    have hfy : (f y : EReal) = (((f y : EReal).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal hytop hybot).symm
    calc
      (f (a • x + b • y) : EReal)
          ≤ (a : EReal) * (f x : EReal) + ((1 - a : ℝ) : EReal) * (f y : EReal) := by
            simpa [hb_eq] using hineq
      _ = ((a * (f x : EReal).toReal + b * (f y : EReal).toReal : ℝ) : EReal) := by
            rw [hb_eq, hfx, hfy, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
            simp
  have hbot :
      (f (a • x + b • y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (a • x + b • y) : EReal) from (f _).2)
  have htop :
      (((a * (f x : EReal).toReal + b * (f y : EReal).toReal : ℝ) : EReal)) ≠ ⊤ := by
    exact (EReal.coe_lt_top _).ne
  exact EReal.toReal_le_toReal hineq' hbot htop

/-- Helper for Corollary 9.15: lower semicontinuity of the EReal-valued function descends to the
real-valued representative when restricted to the effective domain. -/
private lemma lowerSemicontinuousWithinAt_toReal_of_mem_gammaZero
    {f : ℝ → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(ℝ)) {x : ℝ}
    (hx : x ∈ effectiveDomain f) :
    LowerSemicontinuousWithinAt (fun z : ℝ ↦ (f z : EReal).toReal) (effectiveDomain f) x := by
  -- Use lower semicontinuity of `f` itself, then compare `f z` with `((f z).toReal : EReal)` on
  -- the effective domain.
  rw [lowerSemicontinuousWithinAt_iff]
  intro r hr
  have hxtop : (f x : EReal) ≠ ⊤ := ne_of_lt hx
  have hxbot : (f x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hrE : (r : EReal) < (f x : EReal) := by
    rw [← EReal.coe_toReal hxtop hxbot]
    exact EReal.coe_lt_coe_iff.mpr hr
  have hf_lsc := hf.1.lowerSemicontinuousWithinAt (effectiveDomain f) x
  rw [lowerSemicontinuousWithinAt_iff] at hf_lsc
  have hbase :
      {z : ℝ | (r : EReal) < (f z : EReal)} ∈ 𝓝[effectiveDomain f] x :=
    hf_lsc (r : EReal) hrE
  filter_upwards [self_mem_nhdsWithin, hbase] with z hzdom hz
  have hztop : (f z : EReal) ≠ ⊤ := ne_of_lt hzdom
  have hle : (f z : EReal) ≤ (((f z : EReal).toReal : ℝ) : EReal) := EReal.le_coe_toReal hztop
  exact EReal.coe_lt_coe_iff.mp (lt_of_lt_of_le hz hle)

/-- Helper for Corollary 9.15: if an interval-valued domain contains a point to the right of `x`
but `x` is not interior, then the whole domain lies in `Ici x`. -/
private lemma subset_Ici_of_not_mem_interior
    {s : Set ℝ} (hconv : Convex ℝ s) {x y : ℝ}
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y) (hxint : x ∉ interior s) :
    s ⊆ Set.Ici x := by
  -- A point of the domain on the left of `x` would create an open interval around `x`.
  intro z hz
  by_contra hzx
  have hzx' : z < x := by simpa [Set.mem_Ici, not_le] using hzx
  have hIoo : Set.Ioo z y ⊆ s := by
    intro w hw
    exact hconv.ordConnected.out hz hy ⟨hw.1.le, hw.2.le⟩
  have hxIoo : x ∈ Set.Ioo z y := ⟨hzx', hxy⟩
  apply hxint
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds hxIoo) hIoo

/-- Helper for Corollary 9.15: if an interval-valued domain contains a point to the left of `x`
but `x` is not interior, then the whole domain lies in `Iic x`. -/
private lemma subset_Iic_of_not_mem_interior
    {s : Set ℝ} (hconv : Convex ℝ s) {x y : ℝ}
    (hx : x ∈ s) (hy : y ∈ s) (hyx : y < x) (hxint : x ∉ interior s) :
    s ⊆ Set.Iic x := by
  -- The symmetric interval argument rules out any point of the domain strictly to the right.
  intro z hz
  by_contra hxz
  have hxz' : x < z := by simpa [Set.mem_Iic, not_le] using hxz
  have hIoo : Set.Ioo y z ⊆ s := by
    intro w hw
    exact hconv.ordConnected.out hy hz ⟨hw.1.le, hw.2.le⟩
  have hxIoo : x ∈ Set.Ioo y z := ⟨hyx, hxz'⟩
  apply hxint
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds hxIoo) hIoo

/-- Helper for Corollary 9.15: on a right-hand segment `[x,y)`, convexity bounds the increase of
the real-valued representative above its value at `x` by the secant slope through `y`. -/
private lemma sub_toReal_le_right_secant
    {f : ℝ → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(ℝ)) {x y z : ℝ}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    (hxy : x < y) (hzx : x ≤ z) (hzy : z < y) :
    (f z : EReal).toReal - (f x : EReal).toReal ≤
      (|(f y : EReal).toReal - (f x : EReal).toReal| / (y - x)) * |z - x| := by
  -- Write `z` as a convex combination of `x` and `y`, then compare with the secant line.
  by_cases hzx_eq : z = x
  · simp [hzx_eq]
  have hzx' : x < z := lt_of_le_of_ne hzx (Ne.symm hzx_eq)
  let a : ℝ := (y - z) / (y - x)
  let b : ℝ := (z - x) / (y - x)
  have hden : 0 < y - x := sub_pos.mpr hxy
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (sub_pos.mpr hzy) hden
  have hb : 0 < b := by
    dsimp [b]
    exact div_pos (sub_pos.mpr hzx') hden
  have hab : a + b = 1 := by
    dsimp [a, b]
    field_simp [sub_ne_zero.mpr hxy.ne]
    ring
  have hz_repr : a • x + b • y = z := by
    dsimp [a, b]
    field_simp [sub_ne_zero.mpr hxy.ne]
    ring
  have hconv := toReal_weighted_average_le hf hx hy ha hb hab
  have hupper :
      (f z : EReal).toReal - (f x : EReal).toReal ≤
        b * ((f y : EReal).toReal - (f x : EReal).toReal) := by
    rw [hz_repr] at hconv
    calc
      (f z : EReal).toReal - (f x : EReal).toReal
          ≤ (a * (f x : EReal).toReal + b * (f y : EReal).toReal) - (f x : EReal).toReal := by
            exact sub_le_sub_right hconv _
      _ = b * ((f y : EReal).toReal - (f x : EReal).toReal) := by
            have hrewrite :
                (a * (f x : EReal).toReal + b * (f y : EReal).toReal) - (f x : EReal).toReal =
                  b * ((f y : EReal).toReal - (f x : EReal).toReal) := by
              have ha_eq : a = 1 - b := by
                linarith [hab]
              calc
                (a * (f x : EReal).toReal + b * (f y : EReal).toReal) - (f x : EReal).toReal
                    = (((1 - b) * (f x : EReal).toReal) + b * (f y : EReal).toReal) -
                        (f x : EReal).toReal := by rw [ha_eq]
                _ = b * ((f y : EReal).toReal - (f x : EReal).toReal) := by ring
            exact hrewrite
  calc
    (f z : EReal).toReal - (f x : EReal).toReal
        ≤ b * ((f y : EReal).toReal - (f x : EReal).toReal) := hupper
    _ ≤ b * |(f y : EReal).toReal - (f x : EReal).toReal| := by
          exact mul_le_mul_of_nonneg_left (le_abs_self _) hb.le
    _ = (|(f y : EReal).toReal - (f x : EReal).toReal| / (y - x)) * |z - x| := by
          have hz_abs : |z - x| = z - x := abs_of_nonneg (sub_nonneg.mpr hzx)
          rw [hz_abs]
          dsimp [b]
          field_simp [hxy.ne']

/-- Helper for Corollary 9.15: on a left-hand segment `(a,x]`, convexity bounds the increase of
the real-valued representative above its value at `x` by the secant slope through `a`. -/
private lemma sub_toReal_le_left_secant
    {f : ℝ → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(ℝ)) {a x z : ℝ}
    (ha : a ∈ effectiveDomain f) (hx : x ∈ effectiveDomain f)
    (hax : a < x) (haz : a < z) (hzx : z ≤ x) :
    (f z : EReal).toReal - (f x : EReal).toReal ≤
      (|(f a : EReal).toReal - (f x : EReal).toReal| / (x - a)) * |z - x| := by
  -- This is the symmetric secant-line estimate, now using the left endpoint `a`.
  by_cases hzx_eq : z = x
  · simp [hzx_eq]
  have hzx' : z < x := lt_of_le_of_ne hzx hzx_eq
  let α : ℝ := (x - z) / (x - a)
  let β : ℝ := (z - a) / (x - a)
  have hden : 0 < x - a := sub_pos.mpr hax
  have hα : 0 < α := by
    dsimp [α]
    exact div_pos (sub_pos.mpr hzx') hden
  have hβ : 0 < β := by
    dsimp [β]
    exact div_pos (sub_pos.mpr haz) hden
  have hαβ : α + β = 1 := by
    dsimp [α, β]
    field_simp [sub_ne_zero.mpr hax.ne]
    ring
  have hz_repr : α • a + β • x = z := by
    dsimp [α, β]
    field_simp [sub_ne_zero.mpr hax.ne]
    ring
  have hconv := toReal_weighted_average_le hf ha hx hα hβ hαβ
  have hupper :
      (f z : EReal).toReal - (f x : EReal).toReal ≤
        α * ((f a : EReal).toReal - (f x : EReal).toReal) := by
    rw [hz_repr] at hconv
    calc
      (f z : EReal).toReal - (f x : EReal).toReal
          ≤ (α * (f a : EReal).toReal + β * (f x : EReal).toReal) - (f x : EReal).toReal := by
            exact sub_le_sub_right hconv _
      _ = α * ((f a : EReal).toReal - (f x : EReal).toReal) := by
            have hrewrite :
                (α * (f a : EReal).toReal + β * (f x : EReal).toReal) - (f x : EReal).toReal =
                  α * ((f a : EReal).toReal - (f x : EReal).toReal) := by
              have hβ_eq : β = 1 - α := by
                linarith [hαβ]
              calc
                (α * (f a : EReal).toReal + β * (f x : EReal).toReal) - (f x : EReal).toReal
                    = (α * (f a : EReal).toReal + (1 - α) * (f x : EReal).toReal) -
                        (f x : EReal).toReal := by rw [hβ_eq]
                _ = α * ((f a : EReal).toReal - (f x : EReal).toReal) := by ring
            exact hrewrite
  calc
    (f z : EReal).toReal - (f x : EReal).toReal
        ≤ α * ((f a : EReal).toReal - (f x : EReal).toReal) := hupper
    _ ≤ α * |(f a : EReal).toReal - (f x : EReal).toReal| := by
          exact mul_le_mul_of_nonneg_left (le_abs_self _) hα.le
    _ = (|(f a : EReal).toReal - (f x : EReal).toReal| / (x - a)) * |z - x| := by
          have hz_abs : |z - x| = x - z := by
            rw [abs_of_nonpos (sub_nonpos.mpr hzx)]
            ring
          rw [hz_abs]
          dsimp [α]
          field_simp [sub_ne_zero.mpr hax.ne]

-- Proof sketch: the effective domain of a `Γ₀(ℝ)` function is an interval in `ℝ`. At interior
-- points, apply the local continuity part of the convex-function continuity theorem from Chapter 8;
-- at boundary points of the interval, use the one-sided segment convergence result from
-- Proposition 9.14 to obtain continuity relative to the effective domain.
/-- Corollary 9.15: if `f ∈ Γ₀(ℝ)`, then the real-valued representative of `f` is continuous on
its effective domain; equivalently, the restriction `f|_{dom f} : dom f → ℝ` is continuous. -/
theorem continuousOn_toReal_effectiveDomain_of_mem_gammaZero
    {f : ℝ → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(ℝ)) :
    ContinuousOn (fun x : ℝ ↦ (f x : EReal).toReal) (effectiveDomain f) := by
  intro x hx
  let g : ℝ → ℝ := fun z ↦ (f z : EReal).toReal
  have hdom_conv : Convex ℝ (effectiveDomain f) := convex_effectiveDomain_of_mem_gammaZero hf
  have hlsc : LowerSemicontinuousWithinAt g (effectiveDomain f) x :=
    lowerSemicontinuousWithinAt_toReal_of_mem_gammaZero hf hx
  -- Follow the textbook split into interior points and boundary points of the interval domain.
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hlower_event :
      {z : ℝ | g x - ε < g z} ∈ 𝓝[effectiveDomain f] x := by
    rw [lowerSemicontinuousWithinAt_iff] at hlsc
    simpa [g] using hlsc (g x - ε) (by linarith)
  obtain ⟨δl, hδl, hδlsub⟩ := Metric.mem_nhdsWithin_iff.mp hlower_event
  have hlower :
      ∀ ⦃z : ℝ⦄, z ∈ effectiveDomain f → dist z x < δl → g x - ε < g z := by
    intro z hzdom hdist
    exact hδlsub ⟨by simpa [Metric.mem_ball, Real.dist_eq] using hdist, hzdom⟩
  by_cases hxint : x ∈ interior (effectiveDomain f)
  · -- Inside the interval domain, use left and right secant-line upper bounds.
    rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hxint) with ⟨r, hr, hrsub⟩
    let a : ℝ := x - r / 2
    let b : ℝ := x + r / 2
    have ha_mem_ball : a ∈ Metric.ball x r := by
      rw [Metric.mem_ball, Real.dist_eq]
      dsimp [a]
      have hdist : |a - x| = r / 2 := by
        have : a - x = -r / 2 := by
          dsimp [a]
          ring
        rw [this, abs_of_nonpos]
        · ring
        · linarith
      rw [hdist]
      linarith
    have hb_mem_ball : b ∈ Metric.ball x r := by
      rw [Metric.mem_ball, Real.dist_eq]
      dsimp [b]
      have hdist : |b - x| = r / 2 := by
        have : b - x = r / 2 := by
          dsimp [b]
          ring
        rw [this]
        have hr2_nonneg : 0 ≤ r / 2 := by linarith
        rw [abs_of_nonneg hr2_nonneg]
      rw [hdist]
      linarith
    have ha : a ∈ effectiveDomain f := hrsub ha_mem_ball
    have hb : b ∈ effectiveDomain f := hrsub hb_mem_ball
    have hax : a < x := by
      dsimp [a]
      linarith
    have hxb : x < b := by
      dsimp [b]
      linarith
    let Ka : ℝ := |g a - g x| / (x - a)
    let Kb : ℝ := |g b - g x| / (b - x)
    let K : ℝ := max Ka Kb
    have hK_nonneg : 0 ≤ K := by
      have hKa_nonneg : 0 ≤ Ka := by
        dsimp [Ka]
        exact div_nonneg (abs_nonneg _) (by linarith)
      have hKb_nonneg : 0 ≤ Kb := by
        dsimp [Kb]
        exact div_nonneg (abs_nonneg _) (by linarith)
      dsimp [K]
      exact le_trans hKa_nonneg (le_max_left _ _)
    have hKpos : 0 < K + 1 := by linarith
    have hδpos : 0 < min (r / 2) (min (ε / (K + 1)) δl) := by
      refine lt_min (by linarith) ?_
      refine lt_min ?_ hδl
      exact div_pos hε hKpos
    refine ⟨min (r / 2) (min (ε / (K + 1)) δl), hδpos, ?_⟩
    intro z hzdom hdist
    have hdist_r : dist z x < r / 2 := lt_of_lt_of_le hdist (min_le_left _ _)
    have hδ_eps_le : min (r / 2) (min (ε / (K + 1)) δl) ≤ ε / (K + 1) := by
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hδ_l_le : min (r / 2) (min (ε / (K + 1)) δl) ≤ δl := by
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hdist_eps : dist z x < ε / (K + 1) := lt_of_lt_of_le hdist hδ_eps_le
    have hdist_l : dist z x < δl := lt_of_lt_of_le hdist hδ_l_le
    have hupper :
        g z - g x < ε := by
      by_cases hzx : z ≤ x
      · have haz : a < z := by
          have hzclose : |z - x| < r / 2 := by simpa [Real.dist_eq] using hdist_r
          have hzleft : x - z < r / 2 := by
            simpa [abs_of_nonpos (sub_nonpos.mpr hzx)] using hzclose
          dsimp [a]
          linarith
        have hsec := sub_toReal_le_left_secant hf ha hx hax haz hzx
        have hKa_le : Ka ≤ K := by
          dsimp [K]
          exact le_max_left _ _
        have hmul_lt : K * |z - x| < ε := by
          have hzclose : |z - x| < ε / (K + 1) := by simpa [Real.dist_eq] using hdist_eps
          have hscaled : |z - x| * (K + 1) < ε := by
            exact (lt_div_iff₀ hKpos).mp hzclose
          have hKabs_le : K * |z - x| ≤ |z - x| * (K + 1) := by
            nlinarith [hK_nonneg, abs_nonneg (z - x)]
          exact lt_of_le_of_lt hKabs_le (by simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
        have hsec' : g z - g x ≤ K * |z - x| := by
          nlinarith [hsec, hKa_le, abs_nonneg (z - x)]
        exact lt_of_le_of_lt hsec' hmul_lt
      · have hzx' : x ≤ z := le_of_not_ge hzx
        have hzy : z < b := by
          have hzclose : |z - x| < r / 2 := by simpa [Real.dist_eq] using hdist_r
          have hzright : z - x < r / 2 := by
            simpa [abs_of_nonneg (sub_nonneg.mpr hzx')] using hzclose
          dsimp [b]
          linarith
        have hsec := sub_toReal_le_right_secant hf hx hb hxb hzx' hzy
        have hKb_le : Kb ≤ K := by
          dsimp [K]
          exact le_max_right _ _
        have hmul_lt : K * |z - x| < ε := by
          have hzclose : |z - x| < ε / (K + 1) := by simpa [Real.dist_eq] using hdist_eps
          have hscaled : |z - x| * (K + 1) < ε := by
            exact (lt_div_iff₀ hKpos).mp hzclose
          have hKabs_le : K * |z - x| ≤ |z - x| * (K + 1) := by
            nlinarith [hK_nonneg, abs_nonneg (z - x)]
          exact lt_of_le_of_lt hKabs_le (by simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
        have hsec' : g z - g x ≤ K * |z - x| := by
          nlinarith [hsec, hKb_le, abs_nonneg (z - x)]
        exact lt_of_le_of_lt hsec' hmul_lt
    have hlow : g x - ε < g z := hlower hzdom hdist_l
    rw [Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith, hupper⟩
  · -- Outside the interior, the interval domain has points only on one side of `x`.
    by_cases hsingle : effectiveDomain f = {x}
    · refine ⟨1, zero_lt_one, ?_⟩
      intro z hzdom _hdist
      have hz_eq : z = x := by simpa [hsingle] using hzdom
      simpa [hz_eq, Real.dist_eq]
    · have hex : ∃ y, y ∈ effectiveDomain f ∧ y ≠ x := by
        by_contra h
        push_neg at h
        apply hsingle
        ext z
        constructor
        · intro hz
          simpa [h z hz]
        · intro hz
          simpa [Set.mem_singleton_iff.mp hz] using hx
      rcases hex with ⟨y, hy, hy_ne⟩
      rcases lt_or_gt_of_ne hy_ne with hyx | hxy
      · have hsubset : effectiveDomain f ⊆ Set.Iic x :=
          subset_Iic_of_not_mem_interior hdom_conv hx hy hyx hxint
        let K : ℝ := |g y - g x| / (x - y)
        have hK_nonneg : 0 ≤ K := by
          dsimp [K]
          exact div_nonneg (abs_nonneg _) (by linarith)
        have hKpos : 0 < K + 1 := by linarith
        have hδpos : 0 < min (x - y) (min (ε / (K + 1)) δl) := by
          refine lt_min (by linarith) ?_
          refine lt_min ?_ hδl
          exact div_pos hε hKpos
        refine ⟨min (x - y) (min (ε / (K + 1)) δl), hδpos, ?_⟩
        intro z hzdom hdist
        have hδ_eps_le : min (x - y) (min (ε / (K + 1)) δl) ≤ ε / (K + 1) := by
          exact le_trans (min_le_right _ _) (min_le_left _ _)
        have hδ_l_le : min (x - y) (min (ε / (K + 1)) δl) ≤ δl := by
          exact le_trans (min_le_right _ _) (min_le_right _ _)
        have hdist_eps : dist z x < ε / (K + 1) := lt_of_lt_of_le hdist hδ_eps_le
        have hdist_l : dist z x < δl := lt_of_lt_of_le hdist hδ_l_le
        have hzx : z ≤ x := hsubset hzdom
        have hyz : y < z := by
          have hzclose : |z - x| < x - y := by simpa [Real.dist_eq] using lt_of_lt_of_le hdist (min_le_left _ _)
          have hzleft : x - z < x - y := by
            simpa [abs_of_nonpos (sub_nonpos.mpr hzx)] using hzclose
          linarith
        have hsec := sub_toReal_le_left_secant hf hy hx hyx hyz hzx
        have hmul_lt : K * |z - x| < ε := by
          have hzclose : |z - x| < ε / (K + 1) := by simpa [Real.dist_eq] using hdist_eps
          have hscaled : |z - x| * (K + 1) < ε := by
            exact (lt_div_iff₀ hKpos).mp hzclose
          have hKabs_le : K * |z - x| ≤ |z - x| * (K + 1) := by
            nlinarith [hK_nonneg, abs_nonneg (z - x)]
          exact lt_of_le_of_lt hKabs_le (by simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
        have hupper : g z - g x < ε := by
          have hsec' : g z - g x ≤ K * |z - x| := by
            simpa [K, abs_sub_comm] using hsec
          exact lt_of_le_of_lt hsec' hmul_lt
        have hlow : g x - ε < g z := hlower hzdom hdist_l
        rw [Real.dist_eq]
        exact abs_lt.mpr ⟨by linarith, hupper⟩
      · have hsubset : effectiveDomain f ⊆ Set.Ici x :=
          subset_Ici_of_not_mem_interior hdom_conv hx hy hxy hxint
        let K : ℝ := |g y - g x| / (y - x)
        have hK_nonneg : 0 ≤ K := by
          dsimp [K]
          exact div_nonneg (abs_nonneg _) (by linarith)
        have hKpos : 0 < K + 1 := by linarith
        have hδpos : 0 < min (y - x) (min (ε / (K + 1)) δl) := by
          refine lt_min (by linarith) ?_
          refine lt_min ?_ hδl
          exact div_pos hε hKpos
        refine ⟨min (y - x) (min (ε / (K + 1)) δl), hδpos, ?_⟩
        intro z hzdom hdist
        have hδ_eps_le : min (y - x) (min (ε / (K + 1)) δl) ≤ ε / (K + 1) := by
          exact le_trans (min_le_right _ _) (min_le_left _ _)
        have hδ_l_le : min (y - x) (min (ε / (K + 1)) δl) ≤ δl := by
          exact le_trans (min_le_right _ _) (min_le_right _ _)
        have hdist_eps : dist z x < ε / (K + 1) := lt_of_lt_of_le hdist hδ_eps_le
        have hdist_l : dist z x < δl := lt_of_lt_of_le hdist hδ_l_le
        have hzx : x ≤ z := hsubset hzdom
        have hzy : z < y := by
          have hzclose : |z - x| < y - x := by simpa [Real.dist_eq] using lt_of_lt_of_le hdist (min_le_left _ _)
          have hzright : z - x < y - x := by
            simpa [abs_of_nonneg (sub_nonneg.mpr hzx)] using hzclose
          linarith
        have hsec := sub_toReal_le_right_secant hf hx hy hxy hzx hzy
        have hmul_lt : K * |z - x| < ε := by
          have hzclose : |z - x| < ε / (K + 1) := by simpa [Real.dist_eq] using hdist_eps
          have hscaled : |z - x| * (K + 1) < ε := by
            exact (lt_div_iff₀ hKpos).mp hzclose
          have hKabs_le : K * |z - x| ≤ |z - x| * (K + 1) := by
            nlinarith [hK_nonneg, abs_nonneg (z - x)]
          exact lt_of_le_of_lt hKabs_le (by simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
        have hupper : g z - g x < ε := by
          have hsec' : g z - g x ≤ K * |z - x| := by
            simpa [K] using hsec
          exact lt_of_le_of_lt hsec' hmul_lt
        have hlow : g x - ε < g z := hlower hzdom hdist_l
        rw [Real.dist_eq]
        exact abs_lt.mpr ⟨by linarith, hupper⟩

end ERealFunction
