/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_30

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section Linear

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Example 9.32: the recession function vanishes at `0` because every translated
increment at the origin is zero. -/
private theorem recessionFunction_zero_eq_zero
    {f : H → Set.Ioi (⊥ : EReal)} (hdom : (effectiveDomain f).Nonempty) :
    (recessionFunction f hdom 0 : EReal) = 0 := by
  -- Rewrite the defining supremum as the supremum of the singleton `{0}`.
  rw [recessionFunction_apply]
  have hzero_image :
      ((fun x : H ↦ (f x : EReal) - (f x : EReal)) '' effectiveDomain f) = ({0} : Set EReal) := by
    ext a
    constructor
    · intro ha
      rcases ha with ⟨x, hx, rfl⟩
      have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
      have hx_bot : (f x : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
      -- Each effective-domain increment at `0` is the self-difference `f x - f x`.
      have hself : ((f x : EReal) - (f x : EReal)) = 0 := EReal.sub_self hx_top hx_bot
      simp [hself]
    · intro ha
      rcases hdom with ⟨x, hx⟩
      rw [Set.mem_singleton_iff] at ha
      subst a
      have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
      have hx_bot : (f x : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
      have hself : ((f x : EReal) - (f x : EReal)) = 0 := EReal.sub_self hx_top hx_bot
      -- A single effective-domain point already realizes the value `0`.
      refine ⟨x, hx, ?_⟩
      simpa [hself]
  simpa [hzero_image]

/-- Helper for Example 9.32: along a positive ray, the norm ratio
`‖x + α • y‖ / α` converges to `‖y‖`. -/
private theorem ray_norm_div_tendsto_norm
    (x y : H) :
    Filter.Tendsto (fun α : Set.Ioi (0 : ℝ) ↦ ‖x + (α : ℝ) • y‖ / (α : ℝ))
      Filter.atTop (nhds ‖y‖) := by
  -- Rewrite the ratio as the norm of the perturbation `(α⁻¹ • x) + y`.
  have hcoe :
      Filter.Tendsto (fun α : Set.Ioi (0 : ℝ) ↦ (α : ℝ)) Filter.atTop Filter.atTop := by
    simpa [Filter.Tendsto] using (Filter.map_val_Ioi_atTop (0 : ℝ))
  have hinv :
      Filter.Tendsto (fun α : Set.Ioi (0 : ℝ) ↦ ((α : ℝ))⁻¹) Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def] using (tendsto_inv_atTop_zero.comp hcoe)
  have hxconst : Filter.Tendsto (fun _ : Set.Ioi (0 : ℝ) ↦ x) Filter.atTop (nhds x) :=
    tendsto_const_nhds
  have hyconst : Filter.Tendsto (fun _ : Set.Ioi (0 : ℝ) ↦ y) Filter.atTop (nhds y) :=
    tendsto_const_nhds
  have hsum :
      Filter.Tendsto (fun α : Set.Ioi (0 : ℝ) ↦ ((α : ℝ)⁻¹) • x + y)
        Filter.atTop (nhds (((0 : ℝ) • x) + y)) := by
    -- The reciprocal scalar tends to `0`, so the perturbation collapses to `y`.
    exact (hinv.smul hxconst).add hyconst
  have hnorm :
      Filter.Tendsto (fun α : Set.Ioi (0 : ℝ) ↦ ‖((α : ℝ)⁻¹) • x + y‖)
        Filter.atTop (nhds ‖((0 : ℝ) • x) + y‖) :=
    (continuous_norm.tendsto _).comp hsum
  have hEq :
      (fun α : Set.Ioi (0 : ℝ) ↦ ‖x + (α : ℝ) • y‖ / (α : ℝ)) =
        fun α : Set.Ioi (0 : ℝ) ↦ ‖((α : ℝ)⁻¹) • x + y‖ := by
    funext α
    have hα : (0 : ℝ) < (α : ℝ) := α.2
    have hαne : (α : ℝ) ≠ 0 := ne_of_gt hα
    calc
      ‖x + (α : ℝ) • y‖ / (α : ℝ)
          = ‖(α : ℝ) • (((α : ℝ)⁻¹) • x + y)‖ / (α : ℝ) := by
              congr 1
              simpa [smul_add, smul_smul, hαne]
      _ = (|(α : ℝ)| * ‖((α : ℝ)⁻¹) • x + y‖) / (α : ℝ) := by
            rw [norm_smul, Real.norm_eq_abs]
      _ = ‖((α : ℝ)⁻¹) • x + y‖ := by
            simp [abs_of_pos hα, hαne]
  rw [hEq]
  simpa using hnorm

/-- Helper for Example 9.32: if `y ≠ 0`, then the norm of the ray `x + α • y` tends to `+∞`. -/
private theorem ray_norm_tendsto_atTop_of_ne_zero
    (x y : H) (hy : y ≠ 0) :
    Filter.Tendsto (fun α : Set.Ioi (0 : ℝ) ↦ ‖x + (α : ℝ) • y‖)
      Filter.atTop Filter.atTop := by
  -- A positive lower bound for the norm ratio turns the linear growth of `α` into norm growth.
  have hratio := ray_norm_div_tendsto_norm x y
  have hy_norm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  let c : ℝ := ‖y‖ / 2
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hratio_ge :
      ∀ᶠ α : Set.Ioi (0 : ℝ) in Filter.atTop, c ≤ ‖x + (α : ℝ) • y‖ / (α : ℝ) := by
    have hgt :
        ∀ᶠ α : Set.Ioi (0 : ℝ) in Filter.atTop, c < ‖x + (α : ℝ) • y‖ / (α : ℝ) := by
      -- The limit `‖y‖` is strictly above `‖y‖ / 2`.
      apply hratio.eventually
      apply Ioi_mem_nhds
      dsimp [c]
      nlinarith
    filter_upwards [hgt] with α hα
    exact le_of_lt hα
  have hcoe :
      Filter.Tendsto (fun α : Set.Ioi (0 : ℝ) ↦ (α : ℝ)) Filter.atTop Filter.atTop := by
    simpa [Filter.Tendsto] using (Filter.map_val_Ioi_atTop (0 : ℝ))
  refine Filter.tendsto_atTop.mpr ?_
  intro b
  have hαlarge : ∀ᶠ α : Set.Ioi (0 : ℝ) in Filter.atTop, b / c ≤ (α : ℝ) :=
    hcoe.eventually_ge_atTop (b / c)
  filter_upwards [hαlarge, hratio_ge] with α hα hratioα
  have hα_pos : 0 < (α : ℝ) := α.2
  -- Compare `‖x + α • y‖` with the positive multiple `α * c`.
  calc
    b = (b / c) * c := by field_simp [hc_pos.ne']
    _ ≤ (α : ℝ) * c := by gcongr
    _ ≤ (α : ℝ) * (‖x + (α : ℝ) • y‖ / (α : ℝ)) := by gcongr
    _ = ‖x + (α : ℝ) • y‖ := by field_simp [ne_of_gt hα_pos]

/-- Helper for Example 9.32: once the ray norm is nonzero, the scaled ray value factors into the
supercoercive quotient times the norm ratio. -/
private theorem scaled_ray_value_eq_supercoercive_factor_of_norm_ne_zero
    {f : H → Set.Ioi (⊥ : EReal)} (x y : H) (α : Set.Ioi (0 : ℝ))
    (hnorm : ‖x + (α : ℝ) • y‖ ≠ 0) :
    (f (x + (α : ℝ) • y) : EReal) / (α : ℝ) =
      ((f (x + (α : ℝ) • y) : EReal) / ‖x + (α : ℝ) • y‖) *
        (((‖x + (α : ℝ) • y‖ / (α : ℝ) : ℝ) : EReal)) := by
  -- This is the algebraic factorization from equation (9.31), written in `EReal`.
  calc
    (f (x + (α : ℝ) • y) : EReal) / (α : ℝ)
        = (f (x + (α : ℝ) • y) : EReal) * (((1 / (α : ℝ) : ℝ)) : EReal) := by
            rw [div_eq_mul_inv, one_div, EReal.coe_inv]
    _ = (f (x + (α : ℝ) • y) : EReal) *
          ((((‖x + (α : ℝ) • y‖)⁻¹) *
            (‖x + (α : ℝ) • y‖ / (α : ℝ)) : ℝ) : EReal) := by
          congr 1
          field_simp [hnorm]
    _ = (f (x + (α : ℝ) • y) : EReal) *
          ((((‖x + (α : ℝ) • y‖)⁻¹ : ℝ) : EReal) *
            (((‖x + (α : ℝ) • y‖ / (α : ℝ) : ℝ) : EReal))) := by
          rw [EReal.coe_mul]
    _ = ((f (x + (α : ℝ) • y) : EReal) *
          (((‖x + (α : ℝ) • y‖)⁻¹ : ℝ) : EReal)) *
            (((‖x + (α : ℝ) • y‖ / (α : ℝ) : ℝ) : EReal)) := by
          rw [mul_assoc]
    _ = ((f (x + (α : ℝ) • y) : EReal) / ‖x + (α : ℝ) • y‖) *
          (((‖x + (α : ℝ) • y‖ / (α : ℝ) : ℝ) : EReal)) := by
          rfl

/-- Helper for Example 9.32: along any nonzero direction, the scaled ray values
`f (x + α • y) / α` tend to `+∞`. -/
private theorem scaled_ray_values_tendsto_top_of_supercoercive
    {f : H → Set.Ioi (⊥ : EReal)}
    (hsuper :
      Filter.Tendsto (fun x : H ↦ (f x : EReal) / ‖x‖)
        (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds (⊤ : EReal)))
    (x : H) {y : H} (hy : y ≠ 0) :
    Filter.Tendsto
      (fun α : Set.Ioi (0 : ℝ) ↦ (f (x + (α : ℝ) • y) : EReal) / (α : ℝ))
      Filter.atTop (nhds (⊤ : EReal)) := by
  -- Route correction: in the current normed setting, `y ≠ 0` forces `‖y‖ > 0`, so the textbook
  -- ray-growth argument applies without the earlier seminorm obstruction.
  have hy_norm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hratio :
      Filter.Tendsto (fun α : Set.Ioi (0 : ℝ) ↦ ‖x + (α : ℝ) • y‖ / (α : ℝ))
        Filter.atTop (nhds ‖y‖) :=
    ray_norm_div_tendsto_norm x y
  have hray_norm :
      Filter.Tendsto (fun α : Set.Ioi (0 : ℝ) ↦ ‖x + (α : ℝ) • y‖)
        Filter.atTop Filter.atTop :=
    ray_norm_tendsto_atTop_of_ne_zero x y hy
  have hsuper' :
      Filter.Tendsto (fun z : H ↦ (f z : EReal) / ‖z‖)
        (Bornology.cobounded H) (nhds (⊤ : EReal)) := by
    simpa [comap_norm_atTop] using hsuper
  have hray_cobounded :
      Filter.Tendsto (fun α : Set.Ioi (0 : ℝ) ↦ x + (α : ℝ) • y)
        Filter.atTop (Bornology.cobounded H) :=
    (tendsto_norm_atTop_iff_cobounded).1 hray_norm
  have hquot :
      Filter.Tendsto
        (fun α : Set.Ioi (0 : ℝ) ↦ (f (x + (α : ℝ) • y) : EReal) / ‖x + (α : ℝ) • y‖)
        Filter.atTop (nhds (⊤ : EReal)) := by
    -- Compose the supercoercive hypothesis with the ray once the ray norm itself goes to `+∞`.
    simpa using hsuper'.comp hray_cobounded
  have hratio_ereal :
      Filter.Tendsto
        (fun α : Set.Ioi (0 : ℝ) ↦ (((‖x + (α : ℝ) • y‖ / (α : ℝ) : ℝ) : EReal)))
        Filter.atTop (nhds ((‖y‖ : ℝ) : EReal)) :=
    EReal.tendsto_coe.2 hratio
  have hmul_cont :
      ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2)
        ((⊤ : EReal), ((‖y‖ : ℝ) : EReal)) := by
    -- Multiplication is continuous at `(⊤, ‖y‖)` because the second factor is a positive finite
    -- real cast.
    refine EReal.continuousAt_mul ?_ ?_ ?_ ?_
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · refine Or.inr ?_
      exact EReal.coe_ne_zero.2 (ne_of_gt hy_norm_pos)
  have hfactor :
      Filter.Tendsto
        (fun α : Set.Ioi (0 : ℝ) ↦
          ((f (x + (α : ℝ) • y) : EReal) / ‖x + (α : ℝ) • y‖) *
            (((‖x + (α : ℝ) • y‖ / (α : ℝ) : ℝ) : EReal)))
        Filter.atTop (nhds (⊤ : EReal)) := by
    have hprod :
        Filter.Tendsto
          (fun α : Set.Ioi (0 : ℝ) ↦
            ((f (x + (α : ℝ) • y) : EReal) / ‖x + (α : ℝ) • y‖,
              (((‖x + (α : ℝ) • y‖ / (α : ℝ) : ℝ) : EReal))))
          Filter.atTop (nhds ((⊤ : EReal), ((‖y‖ : ℝ) : EReal))) :=
      hquot.prodMk_nhds hratio_ereal
    have htop : (⊤ : EReal) * ((‖y‖ : ℝ) : EReal) = ⊤ := by
      exact EReal.top_mul_of_pos (by exact_mod_cast hy_norm_pos)
    have hmul :
        Filter.Tendsto
          (fun α : Set.Ioi (0 : ℝ) ↦
            ((f (x + (α : ℝ) • y) : EReal) / ‖x + (α : ℝ) • y‖) *
              (((‖x + (α : ℝ) • y‖ / (α : ℝ) : ℝ) : EReal)))
          Filter.atTop (nhds ((⊤ : EReal) * ((‖y‖ : ℝ) : EReal))) :=
      hmul_cont.tendsto.comp hprod
    simpa [htop] using hmul
  have hnorm_nonzero :
      ∀ᶠ α : Set.Ioi (0 : ℝ) in Filter.atTop, ‖x + (α : ℝ) • y‖ ≠ 0 := by
    have hratio_pos :
        ∀ᶠ α : Set.Ioi (0 : ℝ) in Filter.atTop, 0 < ‖x + (α : ℝ) • y‖ / (α : ℝ) := by
      -- A positive limit implies the norm ratio is eventually strictly positive.
      apply hratio.eventually
      apply Ioi_mem_nhds
      simpa using hy_norm_pos
    filter_upwards [hratio_pos] with α hα hzero
    simp [hzero] at hα
  have heq :
      (fun α : Set.Ioi (0 : ℝ) ↦
        ((f (x + (α : ℝ) • y) : EReal) / ‖x + (α : ℝ) • y‖) *
          (((‖x + (α : ℝ) • y‖ / (α : ℝ) : ℝ) : EReal))) =ᶠ[Filter.atTop]
      (fun α : Set.Ioi (0 : ℝ) ↦ (f (x + (α : ℝ) • y) : EReal) / (α : ℝ)) := by
    filter_upwards [hnorm_nonzero] with α hα
    -- On the tail where the ray norm is nonzero, equation (9.31) is an exact identity.
    symm
    exact scaled_ray_value_eq_supercoercive_factor_of_norm_ne_zero x y α hα
  exact hfactor.congr' heq

/-- Example 9.32: if `f ∈ Γ₀(H)` is supercoercive, meaning
`f x / ‖x‖ → +∞` as `‖x‖ → +∞`, then its recession function is the extended-real indicator of
the singleton `{0}`. -/
-- Proof sketch: apply Proposition 9.30 (iii) at a point of the effective domain. For `y = 0`,
-- the recession function vanishes at the origin. For `y ≠ 0`, rewrite the scaled ray values as
-- `‖y‖ * (f (x + α • y) / ‖x + α • y‖) * (‖x + α • y‖ / ‖α • y‖)` and combine the
-- supercoercive hypothesis with the fact that the norm ratio tends to `1`.
theorem recessionFunction_eq_indicator_singleton_zero_of_supercoercive
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hsuper :
      Filter.Tendsto (fun x : H ↦ (f x : EReal) / ‖x‖)
        (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds (⊤ : EReal))) :
    (fun y : H ↦ (recessionFunction f hf.2.nonempty y : EReal)) =
      Set.indicator ({(0 : H)}ᶜ) (fun _ : H ↦ (⊤ : EReal)) := by
  rcases hf.2.nonempty with ⟨x, hx⟩
  funext y
  by_cases hy : y = 0
  · -- At the origin, the recession function is the zero value of the indicator.
    subst hy
    rw [recessionFunction_zero_eq_zero hf.2.nonempty]
    simp
  · -- Away from the origin, Proposition 9.30 (iii) and the ray-growth lemma force the value `⊤`.
    have hscaled_top :
        Filter.Tendsto
          (fun α : Set.Ioi (0 : ℝ) ↦ (f (x + (α : ℝ) • y) : EReal) / (α : ℝ))
          Filter.atTop (nhds (⊤ : EReal)) :=
      scaled_ray_values_tendsto_top_of_supercoercive hsuper x hy
    have hrec :
        (recessionFunction f hf.2.nonempty y : EReal) = ⊤ := by
      -- The scaled ray has the same limit as the recession function by Proposition 9.30 (iii).
      exact tendsto_nhds_unique
        (tendsto_scaled_ray_values_to_recessionFunction (f := f) (hf := hf) (hx := hx) y)
        hscaled_top
    rw [hrec]
    simp [hy]

end Linear

end ERealFunction
