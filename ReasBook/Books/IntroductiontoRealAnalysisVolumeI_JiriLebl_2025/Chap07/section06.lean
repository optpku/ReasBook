/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

universe u v

section Chap07
section Section06

section

variable {X : Type u} [PseudoMetricSpace X]
variable {Y : Type v} [PseudoMetricSpace Y]

/-- Definition 7.6.1. A map `φ : X → Y` between metric spaces is a contraction
if it is `k`-Lipschitz for some `k < 1`, i.e., there exists `k < 1` such that
`dist (φ p) (φ q) ≤ k * dist p q` for all `p, q`. For a self-map `φ : X → X`,
a point `x` is a fixed point when `φ x = x`. -/
def contraction (φ : X → Y) : Prop :=
  ∃ k : NNReal, (k : ℝ) < 1 ∧ LipschitzWith k φ

def fixedPoint (φ : X → X) (x : X) : Prop :=
  φ x = x

omit [PseudoMetricSpace X]

/-- The book's fixed point notion coincides with `Function.IsFixedPt`. -/
theorem fixedPoint_iff_isFixedPt (φ : X → X) (x : X) :
    fixedPoint (X := X) φ x ↔ Function.IsFixedPt φ x := by
  rfl

end

/-- Theorem 7.6.2 (contraction mapping principle or Banach fixed point theorem).
If `(X, d)` is a nonempty complete metric space and `φ : X → X` is a contraction,
then `φ` has a unique fixed point. -/
theorem contraction_unique_fixedPoint
    (X : Type u) [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (φ : X → X) (hφ : contraction (X := X) (Y := X) φ) :
    ∃! x : X, fixedPoint (X := X) φ x := by
  classical
  rcases hφ with ⟨k, hk_lt, hk_lip⟩
  have hk : ContractingWith k φ := ⟨by exact_mod_cast hk_lt, hk_lip⟩
  refine ⟨ContractingWith.fixedPoint (f := φ) hk, ?_, ?_⟩
  · have hx : Function.IsFixedPt φ (ContractingWith.fixedPoint (f := φ) hk) :=
      ContractingWith.fixedPoint_isFixedPt (f := φ) hk
    exact (fixedPoint_iff_isFixedPt (φ := φ) _).2 hx
  · intro y hy
    have hy' : Function.IsFixedPt φ y :=
      (fixedPoint_iff_isFixedPt (φ := φ) y).1 hy
    have hunique := ContractingWith.fixedPoint_unique (f := φ) hk hy'
    simpa using hunique

/-- Theorem 7.6.3 (Picard's theorem on existence and uniqueness).
Let `I = [a, b]` and `J = [c, d]` be closed bounded intervals in `ℝ` with
`x₀ ∈ (a, b)` and `y₀ ∈ (c, d)`. Suppose `F : ℝ → ℝ → ℝ` is continuous on
`I × J` and Lipschitz in the second variable with Lipschitz constant `L`,
meaning `|F x y - F x z| ≤ L * |y - z|` for all `x ∈ I` and `y, z ∈ J`.
Then there exists `h > 0` with `[x₀ - h, x₀ + h] ⊆ I` and a unique differentiable
function `f : ℝ → ℝ` with values in `J` such that `f x₀ = y₀` and
`f' x = F x (f x)` on `[x₀ - h, x₀ + h]`. -/
theorem metric_picard_existence_uniqueness
    {a b c d x₀ y₀ L : ℝ}
    (hI : a ≤ b) (hJ : c ≤ d)
    (hx₀ : x₀ ∈ Set.Ioo a b) (hy₀ : y₀ ∈ Set.Ioo c d)
    (F : ℝ → ℝ → ℝ)
    (hF_cont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d))
    (hL_nonneg : 0 ≤ L)
    (hF_lip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d, ∀ z ∈ Set.Icc c d,
      |F x y - F x z| ≤ L * |y - z|) :
    ∃ h > 0,
      Set.Icc (x₀ - h) (x₀ + h) ⊆ Set.Icc a b ∧
      ∃ f : ℝ → ℝ,
        DifferentiableOn ℝ f (Set.Icc (x₀ - h) (x₀ + h)) ∧
          (∀ x ∈ Set.Icc (x₀ - h) (x₀ + h), f x ∈ Set.Icc c d) ∧
          f x₀ = y₀ ∧
          (∀ x ∈ Set.Icc (x₀ - h) (x₀ + h), HasDerivAt f (F x (f x)) x) ∧
          ∀ g : ℝ → ℝ,
            DifferentiableOn ℝ g (Set.Icc (x₀ - h) (x₀ + h)) →
            (∀ x ∈ Set.Icc (x₀ - h) (x₀ + h), g x ∈ Set.Icc c d) →
            g x₀ = y₀ →
            (∀ x ∈ Set.Icc (x₀ - h) (x₀ + h), HasDerivAt g (F x (g x)) x) →
            Set.EqOn g f (Set.Icc (x₀ - h) (x₀ + h)) := by
  classical
  have _ : a ≤ b := hI
  have _ : c ≤ d := hJ
  -- Compactness of the rectangle gives a uniform bound on `F`.
  have hcompact : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) :=
    (isCompact_Icc).prod isCompact_Icc
  have hnonempty : (Set.Icc a b ×ˢ Set.Icc c d).Nonempty := by
    refine ⟨⟨x₀, y₀⟩, ?_⟩
    exact ⟨Set.Ioo_subset_Icc_self hx₀, Set.Ioo_subset_Icc_self hy₀⟩
  obtain ⟨p, hp, hpmax⟩ := hcompact.exists_isMaxOn hnonempty (hF_cont.norm)
  have hM_max :
      ∀ q ∈ Set.Icc a b ×ˢ Set.Icc c d, ‖F q.1 q.2‖ ≤ ‖F p.1 p.2‖ := by
    simpa [isMaxOn_iff] using hpmax
  set M : ℝ := ‖F p.1 p.2‖ with hM_def
  have hM_nonneg : 0 ≤ M := norm_nonneg _
  have hF_bound :
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d, ‖F x y‖ ≤ M := by
    intro x hx y hy
    have hmax := hM_max ⟨x, y⟩ ⟨hx, hy⟩
    simpa [hM_def] using hmax
  -- Margins in the `x`- and `y`-directions.
  set αx : ℝ := min (x₀ - a) (b - x₀) with hαx
  have hαx_pos : 0 < αx := by
    have hx_left : 0 < x₀ - a := sub_pos.mpr hx₀.1
    have hx_right : 0 < b - x₀ := sub_pos.mpr hx₀.2
    have := lt_min hx_left hx_right
    simpa [hαx] using this
  set αy : ℝ := min (y₀ - c) (d - y₀) with hαy
  have hαy_pos : 0 < αy := by
    have hy_left : 0 < y₀ - c := sub_pos.mpr hy₀.1
    have hy_right : 0 < d - y₀ := sub_pos.mpr hy₀.2
    have := lt_min hy_left hy_right
    simpa [hαy] using this
  -- A convenient positive bound for the integrals and the Picard interval.
  set B : ℝ := M + 1 with hB
  have hB_pos : 0 < B := by linarith
  set hbig : ℝ := min αx (αy / B) with hbig_def
  have hbig_pos : 0 < hbig := by
    have hpos1 : 0 < αy / B := by
      exact div_pos hαy_pos hB_pos
    have := lt_min hαx_pos hpos1
    simpa [hbig_def] using this
  -- Work on the smaller symmetric interval to avoid endpoint issues.
  set h : ℝ := hbig / 2 with h_def
  have hh_pos : 0 < h := by nlinarith
  have h_le_hbig : h ≤ hbig := by nlinarith
  have hbig_le_ax : hbig ≤ αx := by
    simp [hbig_def]
  have hbig_le_left : hbig ≤ x₀ - a := by
    have hαx_le_left : αx ≤ x₀ - a := by
      simp [hαx]
    exact le_trans hbig_le_ax hαx_le_left
  have hbig_le_right : hbig ≤ b - x₀ := by
    have hαx_le_right : αx ≤ b - x₀ := by
      simp [hαx]
    exact le_trans hbig_le_ax hαx_le_right
  have hsubset_big : Set.Icc (x₀ - hbig) (x₀ + hbig) ⊆ Set.Icc a b := by
    refine Set.Icc_subset_Icc ?_ ?_
    · linarith [hbig_le_left]
    · linarith [hbig_le_right]
  have hsubset : Set.Icc (x₀ - h) (x₀ + h) ⊆ Set.Icc a b := by
    refine Set.Icc_subset_Icc ?_ ?_
    · linarith [hbig_le_left, h_le_hbig]
    · linarith [hbig_le_right, h_le_hbig]
  -- Realize the data for the Picard–Lindelöf theorem.
  let aBall : NNReal := ⟨αy, le_of_lt hαy_pos⟩
  let Lnorm : NNReal := ⟨B, le_of_lt hB_pos⟩
  let K : NNReal := ⟨L, hL_nonneg⟩
  have hclosedBall_subset : Metric.closedBall y₀ αy ⊆ Set.Icc c d := by
    have hαy_le_left : αy ≤ y₀ - c := by
      simp [αy]
    have hαy_le_right : αy ≤ d - y₀ := by
      simp [αy]
    intro y hy
    have hy_abs : |y - y₀| ≤ αy := by
      have : dist y y₀ ≤ αy := hy
      simpa [Real.dist_eq] using this
    have hy_ge : y₀ - αy ≤ y := by
      have hneg := (abs_le.mp hy_abs).1
      linarith
    have hy_le : y ≤ y₀ + αy := by
      have hpos := (abs_le.mp hy_abs).2
      linarith
    refine ⟨?_, ?_⟩
    · linarith
    · linarith
  have ht0_big : x₀ ∈ Set.Icc (x₀ - hbig) (x₀ + hbig) := by constructor <;> linarith
  let t₀ : Set.Icc (x₀ - hbig) (x₀ + hbig) := ⟨x₀, ht0_big⟩
  have hIPL :
      IsPicardLindelof (fun t y => F t y) t₀ y₀ aBall 0 Lnorm K := by
    refine
      { lipschitzOnWith := ?_
        continuousOn := ?_
        norm_le := ?_
        mul_max_le := ?_ }
    · intro t ht
      refine LipschitzOnWith.of_dist_le_mul ?_
      intro y hy z hz
      have hyJ : y ∈ Set.Icc c d := hclosedBall_subset hy
      have hzJ : z ∈ Set.Icc c d := hclosedBall_subset hz
      have htI : t ∈ Set.Icc a b := hsubset_big ht
      have h := hF_lip t htI y hyJ z hzJ
      simpa [Real.dist_eq, K] using h
    · intro x hx
      have hxJ : x ∈ Set.Icc c d := hclosedBall_subset hx
      have hmap :
          Set.MapsTo (fun t : ℝ => (t, x))
            (Set.Icc (x₀ - hbig) (x₀ + hbig)) (Set.Icc a b ×ˢ Set.Icc c d) := by
        intro t ht
        exact ⟨hsubset_big ht, hxJ⟩
      have hcont : Continuous fun t : ℝ => (t, x) :=
        continuous_id.prodMk continuous_const
      exact hF_cont.comp hcont.continuousOn hmap
    · intro t ht x hx
      have htI : t ∈ Set.Icc a b := hsubset_big ht
      have hxJ : x ∈ Set.Icc c d := hclosedBall_subset hx
      have hM' : ‖F t x‖ ≤ M := hF_bound t htI x hxJ
      have hMB : ‖F t x‖ ≤ B := by linarith
      simpa [Lnorm] using hMB
    · have hle : hbig ≤ αy / B := by
        simp [hbig_def]
      have hmax :
          max ((x₀ + hbig) - (t₀ : ℝ)) ((t₀ : ℝ) - (x₀ - hbig)) = hbig := by
        simp [t₀, max_self]
      have hprod : B * hbig ≤ αy := by
        have hBne : B ≠ 0 := by linarith [hB_pos]
        have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt hB_pos)
        have hmul' : B * (αy / B) = αy := by
          calc
            B * (αy / B) = B * αy / B := (mul_div_assoc B αy B).symm
            _ = αy := by
              simpa using (mul_div_cancel_left₀ (a := B) (b := αy) hBne)
        simpa [hmul'] using hmul
      have hprod' :
          (Lnorm : ℝ) * max ((x₀ + hbig) - (t₀ : ℝ)) ((t₀ : ℝ) - (x₀ - hbig))
            ≤ (aBall : ℝ) := by
        simpa [Lnorm, aBall, hmax] using hprod
      simpa using hprod'
  -- Construct the Picard fixed point on the big interval.
  have hx_init : y₀ ∈ Metric.closedBall y₀ ((0 : ℝ)) := by simp
  obtain ⟨αsol, hαsol⟩ := ODE.FunSpace.exists_isFixedPt_next hIPL hx_init
  let f : ℝ → ℝ := αsol.compProj
  have hf_cont : Continuous f := by
    simpa [f] using αsol.continuous_compProj
  have hf0 : f x₀ = y₀ := by
    have hx0_mem : x₀ ∈ Set.Icc (x₀ - hbig) (x₀ + hbig) := ht0_big
    have hx0_comp : f x₀ = αsol ⟨x₀, hx0_mem⟩ := by
      simpa [f] using (ODE.FunSpace.compProj_of_mem (α := αsol) (t := x₀) hx0_mem)
    have hinit : αsol t₀ = y₀ := by
      have h :=
        congrArg (fun β => β t₀) (show ODE.FunSpace.next hIPL hx_init αsol = αsol from hαsol)
      simpa [ODE.FunSpace.next_apply₀] using h.symm
    simpa [t₀] using (hx0_comp.trans hinit)
  have hsmall_sub_big :
      Set.Icc (x₀ - h) (x₀ + h) ⊆ Set.Icc (x₀ - hbig) (x₀ + hbig) := by
    intro x hx
    constructor <;> linarith [h_le_hbig, hx.1, hx.2]
  have hf_range_big :
      ∀ t ∈ Set.Icc (x₀ - hbig) (x₀ + hbig), f t ∈ Set.Icc c d := by
    intro t ht
    have ht' : f t ∈ Metric.closedBall y₀ αy := by
      simpa [f] using (αsol.compProj_mem_closedBall hIPL.mul_max_le (t := t))
    exact hclosedBall_subset ht'
  have hf_range :
      ∀ t ∈ Set.Icc (x₀ - h) (x₀ + h), f t ∈ Set.Icc c d := by
    intro t ht
    exact hf_range_big t (hsmall_sub_big ht)
  have hf_derivWithin :
      ∀ t ∈ Set.Icc (x₀ - hbig) (x₀ + hbig),
        HasDerivWithinAt f (F t (f t)) (Set.Icc (x₀ - hbig) (x₀ + hbig)) t := by
    intro t ht
    simpa [f] using (by
      apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hIPL.continuousOn_uncurry
        αsol.continuous_compProj.continuousOn
        (fun _ ht' ↦ αsol.compProj_mem_closedBall hIPL.mul_max_le)
        y₀ ht |>.congr_of_mem _ ht
      intro t' ht'
      nth_rw 1 [← hαsol]
      rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply])
  have h_lt_hbig : h < hbig := by nlinarith [hbig_pos, h_def]
  have hx_big_interior :
      ∀ x ∈ Set.Icc (x₀ - h) (x₀ + h), x ∈ Set.Ioo (x₀ - hbig) (x₀ + hbig) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2, h_lt_hbig]
  have hf_deriv :
      ∀ x ∈ Set.Icc (x₀ - h) (x₀ + h), HasDerivAt f (F x (f x)) x := by
    intro x hx
    have hx_big : x ∈ Set.Icc (x₀ - hbig) (x₀ + hbig) := hsmall_sub_big hx
    have hwithin := hf_derivWithin x hx_big
    have hx_int := hx_big_interior x hx
    exact hwithin.hasDerivAt (Icc_mem_nhds hx_int.1 hx_int.2)
  have hf_diff : DifferentiableOn ℝ f (Set.Icc (x₀ - h) (x₀ + h)) := by
    intro x hx
    exact (hf_deriv x hx).differentiableAt.differentiableWithinAt
  have hf_contOn : ContinuousOn f (Set.Icc (x₀ - h) (x₀ + h)) :=
    hf_cont.continuousOn
  -- Package the result with uniqueness on the smaller interval.
  refine ⟨h, hh_pos, hsubset, ?_⟩
  refine ⟨f, hf_diff, hf_range, hf0, hf_deriv, ?_⟩
  intro g hg_diff hg_range hg0 hg_deriv
  have hg_cont : ContinuousOn g (Set.Icc (x₀ - h) (x₀ + h)) :=
    hg_diff.continuousOn
  have ht0_small : x₀ ∈ Set.Ioo (x₀ - h) (x₀ + h) := by
    constructor <;> linarith [hh_pos]
  have hv :
      ∀ t ∈ Set.Ioo (x₀ - h) (x₀ + h),
        LipschitzOnWith K (fun y => F t y) (Set.Icc c d) := by
    intro t ht
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro y hy z hz
    have htI : t ∈ Set.Icc a b := hsubset (Set.Ioo_subset_Icc_self ht)
    have hdist := hF_lip t htI y hy z hz
    simpa [Real.dist_eq, K] using hdist
  have hf_deriv_Ioo :
      ∀ t ∈ Set.Ioo (x₀ - h) (x₀ + h), HasDerivAt f (F t (f t)) t := by
    intro t ht
    exact hf_deriv t (Set.Ioo_subset_Icc_self ht)
  have hg_deriv_Ioo :
      ∀ t ∈ Set.Ioo (x₀ - h) (x₀ + h), HasDerivAt g (F t (g t)) t := by
    intro t ht
    exact hg_deriv t (Set.Ioo_subset_Icc_self ht)
  have hf_range_Ioo :
      ∀ t ∈ Set.Ioo (x₀ - h) (x₀ + h), f t ∈ Set.Icc c d := by
    intro t ht
    exact hf_range t (Set.Ioo_subset_Icc_self ht)
  have hg_range_Ioo :
      ∀ t ∈ Set.Ioo (x₀ - h) (x₀ + h), g t ∈ Set.Icc c d := by
    intro t ht
    exact hg_range t (Set.Ioo_subset_Icc_self ht)
  have hEqOn_fg : Set.EqOn f g (Set.Icc (x₀ - h) (x₀ + h)) := by
    simpa using
      (ODE_solution_unique_of_mem_Icc (v := fun t y => F t y) (s := fun _ => Set.Icc c d)
        (K := K) (hv := hv) (ht := ht0_small)
        (hf := hf_contOn) (hf' := hf_deriv_Ioo) (hfs := hf_range_Ioo)
        (hg := hg_cont) (hg' := hg_deriv_Ioo) (hgs := hg_range_Ioo)
        (heq := by simp [hf0, hg0]))
  exact hEqOn_fg.symm

end Section06
end Chap07
