/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Prop_8_22.BVBounded
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_15
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.ClosedBallCompactness
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.Embedding

public section

/-!
Theorem 8.16.

This file records the atomic source-facing clauses of Theorem 8.16 on the
canonical `BVCompactness` surface: subcritical `Lᵖ(Ω)` relative compactness,
finite-critical weak relative compactness for `1 < d`, and the one-dimensional
weak-* `L∞(Ω)` endpoint obtained from the source convention
`d / (d - 1) = ∞` when `d = 1`, viewed through the canonical pairing with
`L¹(Ω)`.
-/

namespace VariationalRegularization

namespace BVCompactness

section GeneralDimension

variable {d : ℕ}
variable {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}

/-- Helper for Theorem 8.16: a BV-bounded family in `BV Ω` is contained in a closed ball for the
canonical BV norm. -/
lemma subset_closedBall_of_isBVBounded
    (S : Set (BV Ω))
    (hS : IsBVBounded (BV.toL1 '' S)) :
    ∃ R : ℝ, S ⊆ Metric.closedBall (0 : BV Ω) R := by
  rcases hS.norm_add_totalVariation_le with ⟨C, hC⟩
  refine ⟨max C 0, ?_⟩
  intro u hu
  -- Convert the source-side `‖·‖ + TV` estimate into a bound for the BV norm of `u`.
  rw [Metric.mem_closedBall, dist_zero_right]
  have hbound :
      ((‖u.toL1‖ : ℝ) : EReal) + totalVariation u.toL1 ≤ (C : EReal) := by
    exact hC ⟨u, hu, rfl⟩
  have hbot :
      (((‖u.toL1‖ : ℝ) : EReal) + totalVariation u.toL1) ≠ ⊥ := by
    exact (EReal.add_ne_bot_iff).2 ⟨EReal.coe_ne_bot ‖u.toL1‖, BV.lpTotalVariation_ne_bot u⟩
  have hnorm : ‖u‖ ≤ C := by
    rw [BV.norm_def]
    exact EReal.toReal_le_toReal hbound hbot (EReal.coe_ne_top C)
  exact hnorm.trans (le_max_left C 0)

/-- Helper for Theorem 8.16: the difference of two BV points in one radius-`R` closed ball lies
in the radius-`2R` closed ball. -/
lemma sub_mem_closedBall_two_mul
    {R : ℝ}
    {u v : BV Ω}
    (hu : u ∈ Metric.closedBall (0 : BV Ω) R)
    (hv : v ∈ Metric.closedBall (0 : BV Ω) R) :
    u - v ∈ Metric.closedBall (0 : BV Ω) (2 * R) := by
  -- Rewrite closed-ball membership as BV norm bounds.
  rw [Metric.mem_closedBall, dist_zero_right] at hu hv ⊢
  -- The BV triangle inequality places the difference inside the doubled-radius ball.
  calc
    ‖u - v‖ ≤ ‖u‖ + ‖v‖ := norm_sub_le _ _
    _ ≤ R + R := add_le_add hu hv
    _ = 2 * R := by rw [two_mul]

/-- Helper for Theorem 8.16: on differences, the strict-subcritical embedding keeps the underlying
almost-everywhere class of the `L¹(Ω)` representative. -/
lemma toSubcriticalLp_sub_toAEEqFun
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {p : ENNReal}
    [Fact (1 ≤ p)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hp : p < criticalExponent d)
    (u v : BV Ω) :
    (((toSubcriticalLp (d := d) (Ω := Ω) (p := p) hd hΩ hp u -
        toSubcriticalLp (d := d) (Ω := Ω) (p := p) hd hΩ hp v :
          MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
        (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ)) =
      (((u - v).toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
        (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ) := by
  -- Compare the two `AEEqFun` representatives pointwise almost everywhere.
  apply MeasureTheory.AEEqFun.ext
  filter_upwards with x
  -- The strict-subcritical packaging is transparent on the underlying `L¹(Ω)` representatives.
  simp [toSubcriticalLp_toAEEqFun, BV.toL1_sub]

/-- Helper for Theorem 8.16: the strict-subcritical alias `toSubcriticalLp` agrees pointwise with
the canonical `toLp` map at the same exponent. -/
lemma toLp_eq_toSubcriticalLp
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {p : ENNReal}
    [Fact (1 ≤ p)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hp : p < criticalExponent d)
    (u : BV Ω) :
    toLp (d := d) (Ω := Ω) (p := p) hd hΩ (le_of_lt hp) u =
      toSubcriticalLp (d := d) (Ω := Ω) (p := p) hd hΩ hp u := by
  apply Subtype.ext
  -- Both `Lp` points are represented by the same canonical `L¹` function.
  calc
    ((toLp (d := d) (Ω := Ω) (p := p) hd hΩ (le_of_lt hp) u :
        MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
        (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ) =
      ((u.toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
        (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ) := by
          exact toLp_toAEEqFun (d := d) (Ω := Ω) (p := p) hd hΩ (le_of_lt hp) u
    _ =
      ((toSubcriticalLp (d := d) (Ω := Ω) (p := p) hd hΩ hp u :
          MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
          (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ) := by
            exact (toSubcriticalLp_toAEEqFun (d := d) (Ω := Ω) (p := p) hd hΩ hp u).symm

/-- Helper for Theorem 8.16: in dimensions `d > 1`, differences of BV points in one radius-`R`
closed ball satisfy one uniform critical-exponent bound. -/
lemma subcriticalDifference_uniformCriticalBound
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (h1d : 1 < d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (R : ℝ) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ ⦃u v : BV Ω⦄,
        u ∈ Metric.closedBall (0 : BV Ω) R →
        v ∈ Metric.closedBall (0 : BV Ω) R →
        MeasureTheory.eLpNorm (u - v).toL1 (criticalExponent d) (domainMeasure Ω) ≤
          ENNReal.ofReal C := by
  rcases criticalClosedBall_exactBound (d := d) (Ω := Ω) h1d hΩ (2 * R) with ⟨C, hC, hCball⟩
  refine ⟨C, hC, ?_⟩
  intro u v hu hv
  -- Place the difference in the doubled closed ball, then reuse the exact critical owner.
  exact hCball (sub_mem_closedBall_two_mul hu hv)

/-- Helper for Theorem 8.16: in dimension `d = 1`, differences of BV points in one radius-`R`
closed ball satisfy one uniform essential-supremum bound. -/
lemma subcriticalDifference_uniformEndpointBound
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 1))))
    (R : ℝ) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ ⦃u v : BV Ω⦄,
        u ∈ Metric.closedBall (0 : BV Ω) R →
        v ∈ Metric.closedBall (0 : BV Ω) R →
        ∀ᵐ x ∂domainMeasure Ω, ‖(u - v).toL1 x‖ ≤ C := by
  rcases endpointClosedBall_aeBound (Ω := Ω) hΩ (2 * R) with ⟨C, hC, hCball⟩
  refine ⟨C, hC, ?_⟩
  intro u v hu hv
  -- The endpoint owner applies to the same doubled-ball difference.
  exact hCball (sub_mem_closedBall_two_mul hu hv)

/-- Helper for Theorem 8.16: a uniform modulus phrased through one auxiliary metric image
transfers total boundedness to the target image. -/
lemma totallyBounded_image_of_controlled
    {α β γ : Type*}
    [PseudoMetricSpace β]
    [PseudoMetricSpace γ]
    {s : Set α}
    {g : α → β}
    {f : α → γ}
    (hg : TotallyBounded (g '' s))
    (hmod :
      ∀ ε > 0, ∃ δ > 0, ∀ ⦃u v : α⦄, u ∈ s → v ∈ s →
        dist (g u) (g v) < δ → dist (f u) (f v) < ε) :
    TotallyBounded (f '' s) := by
  classical
  rw [Metric.totallyBounded_iff]
  intro ε hε
  rcases hmod ε hε with ⟨δ, hδ, hmodδ⟩
  rcases Metric.finite_approx_of_totallyBounded hg δ hδ with ⟨t, ht_subset, ht_finite, ht_cover⟩
  letI : Fintype {y // y ∈ t} := ht_finite.fintype
  let center : {y // y ∈ t} → α := fun y ↦ Classical.choose (ht_subset y.property)
  have hcenter_mem : ∀ y : {y // y ∈ t}, center y ∈ s := by
    intro y
    exact (Classical.choose_spec (ht_subset y.property)).1
  have hcenter_eq : ∀ y : {y // y ∈ t}, g (center y) = y.1 := by
    intro y
    exact (Classical.choose_spec (ht_subset y.property)).2
  refine ⟨f '' Set.range center, (Set.finite_range center).image f, ?_⟩
  intro z hz
  rcases hz with ⟨u, hu, rfl⟩
  have hgu : g u ∈ g '' s := ⟨u, hu, rfl⟩
  rcases (by simpa [Set.mem_iUnion] using ht_cover hgu) with ⟨y, hy, hyball⟩
  let y' : {y // y ∈ t} := ⟨y, hy⟩
  have hycenter : dist (g u) (g (center y')) < δ := by
    -- Replace the abstract center by the chosen preimage of the finite `g`-cover point.
    simpa [y', hcenter_eq y'] using hyball
  have hdist : dist (f u) (f (center y')) < ε := hmodδ hu (hcenter_mem y') hycenter
  have hcenter_image : f (center y') ∈ f '' Set.range center := by
    exact ⟨center y', ⟨y', rfl⟩, rfl⟩
  -- Use the same chosen preimage as the `f`-center covering `f u`.
  refine Set.mem_iUnion.2 ⟨f (center y'), ?_⟩
  refine Set.mem_iUnion.2 ⟨hcenter_image, ?_⟩
  exact hdist

/-- Helper for Theorem 8.16: rewrite function subtraction in `Lp.dist_def` to the underlying
`AEEqFun` of the `Lp` difference, so all later estimates can stay on one representative. -/
lemma lpSub_coeFn_aeEq_subAEEqFun
    {α : Type*}
    {_m : MeasurableSpace α}
    {μ : MeasureTheory.Measure α}
    {p : ENNReal}
    (f g : MeasureTheory.Lp ℝ p μ) :
    ((f : α → ℝ) - (g : α → ℝ)) =ᵐ[μ]
      ((((f - g : MeasureTheory.Lp ℝ p μ) : α →ₘ[μ] ℝ) : α → ℝ)) := by
  -- `MeasureTheory.Lp.coeFn_sub` is the exact coercion bridge from function subtraction to the
  -- underlying `AEEqFun` subtraction carried by the `Lp` difference.
  simpa using (MeasureTheory.Lp.coeFn_sub f g).symm

/-- Helper for Theorem 8.16: both the strict-subcritical `Lᵖ` distance and the auxiliary `L¹`
distance are measured on the same BV difference representative. -/
lemma subcriticalDifference_dist_eq_eLpNorm
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {p : ENNReal}
    [Fact (1 ≤ p)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hp : p < criticalExponent d)
    (u v : BV Ω) :
    dist (toSubcriticalLp (d := d) (Ω := Ω) (p := p) hd hΩ hp u)
        (toSubcriticalLp (d := d) (Ω := Ω) (p := p) hd hΩ hp v) =
      (MeasureTheory.eLpNorm
        ((((u - v).toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
          (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ))
        p (domainMeasure Ω)).toReal ∧
    dist u.toL1 v.toL1 =
      (MeasureTheory.eLpNorm
        ((((u - v).toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
          (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ))
        1 (domainMeasure Ω)).toReal := by
  constructor
  · -- Route correction: rewrite the strict-subcritical metric through the `Lp` subtraction bridge
    -- first, then identify that `AEEqFun` with the shared BV difference representative.
    let fu := toSubcriticalLp (d := d) (Ω := Ω) (p := p) hd hΩ hp u
    let fv := toSubcriticalLp (d := d) (Ω := Ω) (p := p) hd hΩ hp v
    let fuv : (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ :=
      ((fu - fv : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
        (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ)
    have hbridge :
        MeasureTheory.eLpNorm
            ((fu : EuclideanSpace ℝ (Fin d) → ℝ) - (fv : EuclideanSpace ℝ (Fin d) → ℝ))
            p (domainMeasure Ω) =
          MeasureTheory.eLpNorm fuv p (domainMeasure Ω) := by
      -- First pass from function subtraction to the underlying `AEEqFun` of the `Lp`
      -- difference, which is the surface where the theorem-local BV bridge lives.
      exact
        MeasureTheory.eLpNorm_congr_ae
          (by simpa [fu, fv, fuv] using lpSub_coeFn_aeEq_subAEEqFun fu fv)
    have hrep :
        fuv =
          (((u - v).toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
            (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ) := by
      -- The strict-subcritical embedding difference carries exactly the BV difference
      -- representative supplied by `toSubcriticalLp_sub_toAEEqFun`.
      simpa [fu, fv, fuv] using
        toSubcriticalLp_sub_toAEEqFun (d := d) (Ω := Ω) (p := p) hd hΩ hp u v
    rw [MeasureTheory.Lp.dist_def]
    congr 1
    calc
      MeasureTheory.eLpNorm
          ((fu : EuclideanSpace ℝ (Fin d) → ℝ) - (fv : EuclideanSpace ℝ (Fin d) → ℝ))
          p (domainMeasure Ω) =
        MeasureTheory.eLpNorm fuv p (domainMeasure Ω) := hbridge
      _ =
        MeasureTheory.eLpNorm
          ((((u - v).toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
            (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ)) p (domainMeasure Ω) := by
            simpa using
              congrArg
                (fun z : (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ =>
                  MeasureTheory.eLpNorm z p (domainMeasure Ω))
                hrep
  · -- The same transport now collapses the auxiliary `L¹` distance to the identical BV difference
    -- representative, so both distances are measured on the same function.
    let fuv : (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ :=
      ((u.toL1 - v.toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
        (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ)
    have hL1 :
        MeasureTheory.eLpNorm
            ((u.toL1 : EuclideanSpace ℝ (Fin d) → ℝ) -
              (v.toL1 : EuclideanSpace ℝ (Fin d) → ℝ))
            1 (domainMeasure Ω) =
          MeasureTheory.eLpNorm
            ((((u - v).toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
              (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ))
            1 (domainMeasure Ω) := by
      calc
        MeasureTheory.eLpNorm
            ((u.toL1 : EuclideanSpace ℝ (Fin d) → ℝ) -
              (v.toL1 : EuclideanSpace ℝ (Fin d) → ℝ))
            1 (domainMeasure Ω) =
          MeasureTheory.eLpNorm fuv 1 (domainMeasure Ω) := by
            -- The auxiliary `L¹` metric uses the same subtraction bridge as the strict-subcritical
            -- metric, only at exponent `1`.
            exact
              MeasureTheory.eLpNorm_congr_ae
                (by simpa [fuv] using lpSub_coeFn_aeEq_subAEEqFun u.toL1 v.toL1)
        _ =
          MeasureTheory.eLpNorm
            ((((u - v).toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
              (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ))
            1 (domainMeasure Ω) := by
            -- `BV.toL1_sub` identifies the auxiliary `L¹` difference with the same BV
            -- representative used on the strict-subcritical side.
            simpa [fuv, BV.toL1_sub]
    simpa [MeasureTheory.Lp.dist_def] using congrArg ENNReal.toReal hL1

/-- Helper for Theorem 8.16: an almost-everywhere bound `‖f x‖ ≤ C` turns the `L¹` seminorm of
`x ↦ ‖f x‖ ^ p.toReal` into a multiple of the `L¹` seminorm of `f`. -/
lemma eLpNormPower_le_mul_eLpNormOne_of_aeBound
    {α : Type*}
    {_m : MeasurableSpace α}
    {μ : MeasureTheory.Measure α}
    {p : ENNReal}
    (hp1 : 1 ≤ p)
    (hp_top : p ≠ (⊤ : ENNReal))
    {f : α → ℝ}
    {C : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    MeasureTheory.eLpNorm (fun x ↦ ‖f x‖ ^ p.toReal) 1 μ ≤
      ENNReal.ofReal (C ^ (p.toReal - 1)) * MeasureTheory.eLpNorm f 1 μ := by
  have hp_pow_nonneg : 0 ≤ p.toReal - 1 := by
    have hp_toReal : 1 ≤ p.toReal := ENNReal.toReal_mono hp_top hp1
    linarith
  -- Compare the pointwise `p`-power by peeling off one factor of `‖f x‖`.
  have hpointwise :
      ∀ᵐ x ∂μ, ‖‖f x‖ ^ p.toReal‖ ≤ C ^ (p.toReal - 1) * ‖f x‖ := by
    filter_upwards [hbound] with x hx
    have hfx_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
    calc
      ‖‖f x‖ ^ p.toReal‖ = ‖f x‖ ^ p.toReal := by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg hfx_nonneg _)]
      _ = ‖f x‖ ^ (p.toReal - 1) * ‖f x‖ := by
        rw [show p.toReal = (p.toReal - 1) + 1 by ring]
        rw [Real.rpow_add_of_nonneg hfx_nonneg hp_pow_nonneg zero_le_one]
        rw [Real.rpow_one]
        ring
      _ ≤ C ^ (p.toReal - 1) * ‖f x‖ := by
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hfx_nonneg hx hp_pow_nonneg) hfx_nonneg
  -- Apply the monotonicity lemma at exponent `1`.
  exact
    MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpointwise 1

/-- Helper for Theorem 8.16: in dimension `d = 1`, small `L¹(Ω)` differences on one BV closed
ball force small strict-subcritical `Lᵖ(Ω)` differences. -/
lemma subcriticalDifference_small_of_l1_small_endpoint
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {p : ENNReal}
    [Fact (1 ≤ p)]
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 1))))
    (hp : p < criticalExponent 1)
    (R : ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ ⦃u v : BV Ω⦄,
      u ∈ Metric.closedBall (0 : BV Ω) R →
      v ∈ Metric.closedBall (0 : BV Ω) R →
      dist u.toL1 v.toL1 < δ →
      dist (toSubcriticalLp (d := 1) (Ω := Ω) (p := p) (Nat.le_refl 1) hΩ hp u)
        (toSubcriticalLp (d := 1) (Ω := Ω) (p := p) (Nat.le_refl 1) hΩ hp v) < ε := by
  intro ε hε
  by_cases hp1 : p = 1
  · subst hp1
    refine ⟨ε, hε, ?_⟩
    intro u v hu hv huv
    have hu_eq :
        toSubcriticalLp (d := 1) (Ω := Ω) (p := (1 : ENNReal)) (Nat.le_refl 1) hΩ hp u = u.toL1 := by
      -- At exponent `1`, the endpoint strict-subcritical embedding is just the canonical `L¹` point.
      apply Subtype.ext
      simpa using
        toSubcriticalLp_toAEEqFun
          (d := 1) (Ω := Ω) (p := (1 : ENNReal)) (Nat.le_refl 1) hΩ hp u
    have hv_eq :
        toSubcriticalLp (d := 1) (Ω := Ω) (p := (1 : ENNReal)) (Nat.le_refl 1) hΩ hp v = v.toL1 := by
      -- The same identification holds for the second endpoint BV point.
      apply Subtype.ext
      simpa using
        toSubcriticalLp_toAEEqFun
          (d := 1) (Ω := Ω) (p := (1 : ENNReal)) (Nat.le_refl 1) hΩ hp v
    -- After identifying both strict-subcritical points with their `L¹` representatives, the
    -- required estimate is exactly the assumed `L¹` closeness.
    simpa [hu_eq, hv_eq] using huv
  · have hp_top : p ≠ (⊤ : ENNReal) := by
      -- In dimension `1`, strict subcriticality means exactly `p < ∞`.
      simpa [criticalExponent_one] using (ne_of_lt hp)
    rcases subcriticalDifference_uniformEndpointBound (Ω := Ω) hΩ R with ⟨C, hC, hCball⟩
    let K : ℝ := max C 1
    have hK_nonneg : 0 ≤ K := le_trans hC (le_max_left C 1)
    have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
    have hp_ne_zero : p ≠ 0 := by
      exact (lt_of_lt_of_le zero_lt_one (show (1 : ENNReal) ≤ p from Fact.out)).ne'
    have hp_toReal_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
    have hp_toReal_gt_one : 1 < p.toReal := by
      exact
        (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2
          (lt_of_le_of_ne Fact.out (by simpa [eq_comm] using hp1))
    refine ⟨ε ^ p.toReal / (K ^ (p.toReal - 1) + 1), by positivity, ?_⟩
    intro u v hu hv huv
    let w : (EuclideanSpace ℝ (Fin 1)) →ₘ[domainMeasure Ω] ℝ :=
      (((u - v).toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
        (EuclideanSpace ℝ (Fin 1)) →ₘ[domainMeasure Ω] ℝ)
    rcases
        subcriticalDifference_dist_eq_eLpNorm
          (d := 1) (Ω := Ω) (p := p) (Nat.le_refl 1) hΩ hp u v with
      ⟨hdistp, hdist1⟩
    have hw_bound : ∀ᵐ x ∂domainMeasure Ω, ‖w x‖ ≤ K := by
      filter_upwards [hCball hu hv] with x hx
      exact hx.trans (le_max_left C 1)
    have hpow :
        MeasureTheory.eLpNorm w p (domainMeasure Ω) ^ p.toReal ≤
          ENNReal.ofReal (K ^ (p.toReal - 1)) *
            MeasureTheory.eLpNorm w 1 (domainMeasure Ω) := by
      calc
        MeasureTheory.eLpNorm w p (domainMeasure Ω) ^ p.toReal =
            MeasureTheory.eLpNorm (fun x ↦ ‖w x‖ ^ p.toReal) 1 (domainMeasure Ω) := by
              rw [MeasureTheory.eLpNorm_norm_rpow (f := fun x ↦ w x) (p := (1 : ENNReal))
                hp_toReal_pos, ENNReal.ofReal_toReal hp_top, one_mul]
        _ ≤ ENNReal.ofReal (K ^ (p.toReal - 1)) *
              MeasureTheory.eLpNorm (fun x ↦ w x) 1 (domainMeasure Ω) :=
            eLpNormPower_le_mul_eLpNormOne_of_aeBound
              (p := p) Fact.out hp_top hw_bound
        _ = ENNReal.ofReal (K ^ (p.toReal - 1)) *
              MeasureTheory.eLpNorm w 1 (domainMeasure Ω) := by rfl
    have hw_one_ne_top :
        MeasureTheory.eLpNorm w 1 (domainMeasure Ω) ≠ ⊤ := by
      simpa [w, BV.toL1_sub] using MeasureTheory.Lp.eLpNorm_ne_top (u.toL1 - v.toL1)
    have hpow_real :
        (MeasureTheory.eLpNorm w p (domainMeasure Ω)).toReal ^ p.toReal ≤
          K ^ (p.toReal - 1) * (MeasureTheory.eLpNorm w 1 (domainMeasure Ω)).toReal := by
      have hKpow_nonneg : 0 ≤ K ^ (p.toReal - 1) := Real.rpow_nonneg hK_nonneg _
      have hpow_toReal :=
        ENNReal.toReal_mono
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hw_one_ne_top)
          hpow
      simpa [ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hKpow_nonneg] using
        hpow_toReal
    have hdist_pow :
        dist
            (toSubcriticalLp (d := 1) (Ω := Ω) (p := p) (Nat.le_refl 1) hΩ hp u)
            (toSubcriticalLp (d := 1) (Ω := Ω) (p := p) (Nat.le_refl 1) hΩ hp v) ^ p.toReal ≤
          K ^ (p.toReal - 1) * dist u.toL1 v.toL1 := by
      simpa [w, hdistp, hdist1] using hpow_real
    have hdist_pow_lt :
        dist
            (toSubcriticalLp (d := 1) (Ω := Ω) (p := p) (Nat.le_refl 1) hΩ hp u)
            (toSubcriticalLp (d := 1) (Ω := Ω) (p := p) (Nat.le_refl 1) hΩ hp v) ^ p.toReal <
          ε ^ p.toReal := by
      calc
        dist
            (toSubcriticalLp (d := 1) (Ω := Ω) (p := p) (Nat.le_refl 1) hΩ hp u)
            (toSubcriticalLp (d := 1) (Ω := Ω) (p := p) (Nat.le_refl 1) hΩ hp v) ^ p.toReal ≤
          K ^ (p.toReal - 1) * dist u.toL1 v.toL1 := hdist_pow
        _ < K ^ (p.toReal - 1) * (ε ^ p.toReal / (K ^ (p.toReal - 1) + 1)) := by
          gcongr
        _ < ε ^ p.toReal := by
          have hfrac :
              K ^ (p.toReal - 1) / (K ^ (p.toReal - 1) + 1) < 1 := by
            have hpow_nonneg : 0 ≤ K ^ (p.toReal - 1) := Real.rpow_nonneg hK_nonneg _
            have hden_pos : 0 < K ^ (p.toReal - 1) + 1 := by positivity
            exact (div_lt_one hden_pos).2 (by linarith)
          have heps_pow_pos : 0 < ε ^ p.toReal := Real.rpow_pos_of_pos hε _
          have hmul_lt :
              ε ^ p.toReal * (K ^ (p.toReal - 1) / (K ^ (p.toReal - 1) + 1)) < ε ^ p.toReal := by
            nlinarith [mul_lt_mul_of_pos_left hfrac heps_pow_pos]
          have hrewrite :
              K ^ (p.toReal - 1) * (ε ^ p.toReal / (K ^ (p.toReal - 1) + 1)) =
                ε ^ p.toReal * (K ^ (p.toReal - 1) / (K ^ (p.toReal - 1) + 1)) := by
            ring
          rw [hrewrite]
          exact hmul_lt
    -- Compare `p`-powers on nonnegative distances, then peel off the positive exponent `p.toReal`.
    exact
      (Real.rpow_lt_rpow_iff dist_nonneg (le_of_lt hε) hp_toReal_pos).1
        (by simpa using hdist_pow_lt)

/-- Helper for Theorem 8.16: split an intermediate power into a low-amplitude linear part and a
high-amplitude `b`-power tail at one positive threshold. -/
lemma intermediatePower_le_thresholdLinear_add_highPower
    {x T a b : ℝ}
    (hx : 0 ≤ x)
    (hT : 0 < T)
    (ha_one : 1 < a)
    (hab : a < b) :
    x ^ a ≤ T ^ (a - 1) * x + T ^ (a - b) * x ^ b := by
  by_cases hxt : x ≤ T
  · have ha_sub_nonneg : 0 ≤ a - 1 := by linarith
    have hxa :
        x ^ a = x ^ (a - 1) * x := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (Real.rpow_add_of_nonneg hx ha_sub_nonneg zero_le_one (x := x))
    have hpow :
        x ^ (a - 1) ≤ T ^ (a - 1) := Real.rpow_le_rpow hx hxt ha_sub_nonneg
    have htail_nonneg : 0 ≤ T ^ (a - b) * x ^ b := by
      positivity
    -- On the region `x ≤ T`, absorb the whole `x^a` term into the linear threshold part.
    calc
      x ^ a = x ^ (a - 1) * x := hxa
      _ ≤ T ^ (a - 1) * x := by gcongr
      _ ≤ T ^ (a - 1) * x + T ^ (a - b) * x ^ b := by linarith
  · have hTx : T ≤ x := le_of_not_ge hxt
    have hx_pos : 0 < x := lt_of_lt_of_le hT hTx
    have hxb_nonneg : 0 ≤ x ^ b := Real.rpow_nonneg hx b
    have hlin_nonneg : 0 ≤ T ^ (a - 1) * x := by
      positivity
    have hpow :
        x ^ (a - b) ≤ T ^ (a - b) := by
      exact Real.rpow_le_rpow_of_nonpos hT hTx (by linarith)
    have hxa :
        x ^ a = x ^ b * x ^ (a - b) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (Real.rpow_add hx_pos b (a - b))
    -- On the tail `T ≤ x`, keep the high-power part and bound the negative exponent by monotonicity.
    calc
      x ^ a = x ^ b * x ^ (a - b) := hxa
      _ ≤ x ^ b * T ^ (a - b) := by gcongr
      _ = T ^ (a - b) * x ^ b := by ring
      _ ≤ T ^ (a - 1) * x + T ^ (a - b) * x ^ b := by linarith

/-- Helper for Theorem 8.16: interpolation between `L¹` and `L^q` controls the `p`-power of an
intermediate `Lᵖ` seminorm. -/
lemma eLpNormInterpolateOneHigh
    {α : Type*}
    {_m : MeasurableSpace α}
    {μ : MeasureTheory.Measure α}
    {w : α → ℝ}
    {p q : ENNReal}
    (hw1 : MeasureTheory.MemLp w 1 μ)
    (hwq : MeasureTheory.MemLp w q μ)
    (hp_one : 1 < p.toReal)
    (hpq : p.toReal < q.toReal)
    (hq_top : q ≠ (⊤ : ENNReal))
    {T : ℝ}
    (hT : 0 < T) :
    (MeasureTheory.eLpNorm w p μ).toReal ^ p.toReal ≤
      T ^ (p.toReal - 1) * (MeasureTheory.eLpNorm w 1 μ).toReal +
        T ^ (p.toReal - q.toReal) * (MeasureTheory.eLpNorm w q μ).toReal ^ q.toReal := by
  have hp_top : p ≠ (⊤ : ENNReal) := by
    intro hp_top
    rw [hp_top, ENNReal.toReal_top] at hp_one
    linarith
  have hp_ne_zero : p ≠ 0 := by
    intro hp_zero
    rw [hp_zero, ENNReal.toReal_zero] at hp_one
    linarith
  have hp_toReal_pos : 0 < p.toReal := by linarith
  have hq_toReal_pos : 0 < q.toReal := lt_trans hp_toReal_pos hpq
  have hq_ne_zero : q ≠ 0 := by
    intro hq_zero
    simpa [hq_zero] using hq_toReal_pos
  -- Route correction: the real-variable threshold split is now isolated in
  -- `intermediatePower_le_thresholdLinear_add_highPower`; the remaining work is to transport that
  -- inequality through `MeasureTheory.eLpNorm_one_eq_lintegral_enorm` and
  -- `MeasureTheory.eLpNorm_norm_rpow`.
  let A : ℝ := T ^ (p.toReal - 1)
  let B : ℝ := T ^ (p.toReal - q.toReal)
  have hA_nonneg : 0 ≤ A := by
    -- The low-amplitude threshold coefficient is nonnegative because `T > 0`.
    dsimp [A]
    positivity
  have hB_nonneg : 0 ≤ B := by
    -- The high-power threshold coefficient is also nonnegative on the positive threshold.
    dsimp [B]
    positivity
  have hw_enorm_aemeas : AEMeasurable (fun x ↦ ‖w x‖ₑ) μ := hw1.enorm.aemeasurable
  have hwq_rpow_aemeas : AEMeasurable (fun x ↦ ‖w x‖ₑ ^ q.toReal) μ := by
    -- The `q`-power tail is measurable because the `L^q` datum already controls the norm field.
    exact hwq.enorm.aemeasurable.pow_const q.toReal
  have hpointwise :
      ∀ᵐ x ∂μ, ‖w x‖ₑ ^ p.toReal ≤
        ENNReal.ofReal A * ‖w x‖ₑ + ENNReal.ofReal B * ‖w x‖ₑ ^ q.toReal := by
    filter_upwards with x
    -- Lift the real threshold split to the `ℝ≥0∞` integrand surface used by `eLpNorm`.
    have hx :
        ENNReal.ofReal (‖w x‖ ^ p.toReal) ≤
          ENNReal.ofReal (A * ‖w x‖ + B * ‖w x‖ ^ q.toReal) := by
      exact
        ENNReal.ofReal_le_ofReal
          (intermediatePower_le_thresholdLinear_add_highPower
            (x := ‖w x‖)
            (T := T)
            (a := p.toReal)
            (b := q.toReal)
            (norm_nonneg _)
            hT
            hp_one
            hpq)
    have hAx_nonneg : 0 ≤ A * ‖w x‖ := by positivity
    have hBx_nonneg : 0 ≤ B * ‖w x‖ ^ q.toReal := by positivity
    have hnorm_enorm : ‖w x‖ₑ = ENNReal.ofReal ‖w x‖ := by
      simpa using (ofReal_norm (w x)).symm
    calc
      ‖w x‖ₑ ^ p.toReal = ENNReal.ofReal (‖w x‖ ^ p.toReal) := by
        rw [hnorm_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (w x)) ENNReal.toReal_nonneg]
      _ ≤ ENNReal.ofReal (A * ‖w x‖ + B * ‖w x‖ ^ q.toReal) := hx
      _ = ENNReal.ofReal A * ‖w x‖ₑ + ENNReal.ofReal B * ‖w x‖ₑ ^ q.toReal := by
        rw [ENNReal.ofReal_add hAx_nonneg hBx_nonneg]
        rw [ENNReal.ofReal_mul hA_nonneg, ENNReal.ofReal_mul hB_nonneg]
        rw [hnorm_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (w x)) ENNReal.toReal_nonneg]
  have hlintegral :
      ∫⁻ x, ‖w x‖ₑ ^ p.toReal ∂μ ≤
        ENNReal.ofReal A * ∫⁻ x, ‖w x‖ₑ ∂μ +
          ENNReal.ofReal B * ∫⁻ x, ‖w x‖ₑ ^ q.toReal ∂μ := by
    -- Integrate the pointwise threshold decomposition and pull constants outside the lintegrals.
    calc
      ∫⁻ x, ‖w x‖ₑ ^ p.toReal ∂μ ≤
          ∫⁻ x, (ENNReal.ofReal A * ‖w x‖ₑ + ENNReal.ofReal B * ‖w x‖ₑ ^ q.toReal) ∂μ :=
        MeasureTheory.lintegral_mono_ae hpointwise
      _ = ∫⁻ x, ENNReal.ofReal A * ‖w x‖ₑ ∂μ +
            ∫⁻ x, ENNReal.ofReal B * ‖w x‖ₑ ^ q.toReal ∂μ := by
          rw [MeasureTheory.lintegral_add_right' _ (hwq_rpow_aemeas.const_mul _)]
      _ = ENNReal.ofReal A * ∫⁻ x, ‖w x‖ₑ ∂μ +
            ENNReal.ofReal B * ∫⁻ x, ‖w x‖ₑ ^ q.toReal ∂μ := by
          rw [MeasureTheory.lintegral_const_mul'' _ hw_enorm_aemeas,
            MeasureTheory.lintegral_const_mul'' _ hwq_rpow_aemeas]
  have hqpow :
      ∫⁻ x, ‖w x‖ₑ ^ q.toReal ∂μ =
        MeasureTheory.eLpNorm w q μ ^ q.toReal := by
    -- Rewrite the `q`-power lintegral back to the canonical `eLpNorm` quantity.
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hq_ne_zero hq_top]
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq_toReal_pos.ne', ENNReal.rpow_one]
  have hpow :
      MeasureTheory.eLpNorm w p μ ^ p.toReal ≤
        ENNReal.ofReal A * MeasureTheory.eLpNorm w 1 μ +
          ENNReal.ofReal B * (MeasureTheory.eLpNorm w q μ ^ q.toReal) := by
    -- Express both sides on the same `lintegral` surface before returning to `eLpNorm`.
    calc
      MeasureTheory.eLpNorm w p μ ^ p.toReal = ∫⁻ x, ‖w x‖ₑ ^ p.toReal ∂μ := by
        rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top]
        rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp_toReal_pos.ne', ENNReal.rpow_one]
      _ ≤ ENNReal.ofReal A * ∫⁻ x, ‖w x‖ₑ ∂μ +
            ENNReal.ofReal B * ∫⁻ x, ‖w x‖ₑ ^ q.toReal ∂μ := hlintegral
      _ = ENNReal.ofReal A * MeasureTheory.eLpNorm w 1 μ +
            ENNReal.ofReal B * (MeasureTheory.eLpNorm w q μ ^ q.toReal) := by
          rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm, hqpow]
  have hqpow_ne_top : MeasureTheory.eLpNorm w q μ ^ q.toReal ≠ ⊤ := by
    -- The `L^q` hypothesis guarantees finiteness of the high-power tail term.
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg (ne_of_lt hwq.2)
  have hleft_ne_top :
      ENNReal.ofReal A * MeasureTheory.eLpNorm w 1 μ ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt hw1.2)
  have hright_ne_top :
      ENNReal.ofReal B * (MeasureTheory.eLpNorm w q μ ^ q.toReal) ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hqpow_ne_top
  have hpow_toReal :=
    ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hleft_ne_top, hright_ne_top⟩) hpow
  -- Move back from `ℝ≥0∞` to the real-valued `toReal` norm surface used by the target statement.
  simpa [A, B, ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA_nonneg,
    ENNReal.toReal_ofReal hB_nonneg, ENNReal.toReal_add hleft_ne_top hright_ne_top] using
    hpow_toReal

/-- Helper for Theorem 8.16: a uniform `L^q` bound upgrades sufficiently small `L¹` norm to a
small strict-subcritical `Lᵖ` norm. -/
lemma interpolationThresholdChoice
    {a b C ε : ℝ}
    (ha : 1 < a)
    (hab : a < b)
    (hC : 0 ≤ C)
    (hε : 0 < ε) :
    ∃ T > 0, ∃ δ > 0,
      T ^ (a - 1) * δ + T ^ (a - b) * C ^ b < ε ^ a := by
  have hab_pos : 0 < b - a := sub_pos.mpr hab
  have hεa_half_pos : 0 < ε ^ a / 2 := by
    positivity
  have htail_tendsto :
      Filter.Tendsto (fun T : ℝ ↦ T ^ (a - b) * C ^ b) Filter.atTop (nhds 0) := by
    -- The negative exponent `a - b` forces the tail term to vanish as `T → ∞`.
    have hpow_tendsto : Filter.Tendsto (fun T : ℝ ↦ T ^ (a - b)) Filter.atTop (nhds 0) := by
      simpa [sub_eq_add_neg, add_comm] using tendsto_rpow_neg_atTop hab_pos
    simpa [mul_comm] using hpow_tendsto.mul_const (C ^ b)
  have htail_eventually :
      ∀ᶠ T : ℝ in Filter.atTop, 1 ≤ T ∧ T ^ (a - b) * C ^ b < ε ^ a / 2 := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
      htail_tendsto.eventually (Metric.ball_mem_nhds 0 hεa_half_pos)] with T hT hball
    constructor
    · exact hT
    · have hT_nonneg : 0 ≤ T := le_trans (by norm_num) hT
      have htail_nonneg : 0 ≤ T ^ (a - b) * C ^ b := by
        positivity
      -- Once `T` is positive, the ball estimate around `0` is the desired upper bound.
      simpa [Metric.mem_ball, Real.dist_eq, sub_zero, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hT_nonneg _), abs_of_nonneg (Real.rpow_nonneg hC _),
        abs_of_nonneg htail_nonneg] using hball
  rcases Filter.eventually_atTop.1 htail_eventually with ⟨T, hT⟩
  have hT_ge : 1 ≤ T := (hT T le_rfl).1
  have htail_lt : T ^ (a - b) * C ^ b < ε ^ a / 2 := (hT T le_rfl).2
  have hT_pos : 0 < T := lt_of_lt_of_le zero_lt_one hT_ge
  let δ : ℝ := (ε ^ a / 2) / T ^ (a - 1)
  have hTpow_pos : 0 < T ^ (a - 1) := Real.rpow_pos_of_pos hT_pos _
  have hδ_pos : 0 < δ := by
    -- Spend half of the `ε^a` budget on the `L¹` contribution.
    dsimp [δ]
    positivity
  refine ⟨T, hT_pos, δ, hδ_pos, ?_⟩
  have hmain :
      T ^ (a - 1) * δ = ε ^ a / 2 := by
    -- The chosen `δ` makes the threshold-linear term exactly half of the target budget.
    rw [show δ = (ε ^ a / 2) / T ^ (a - 1) by rfl, mul_div_cancel₀ _ hTpow_pos.ne']
  calc
    T ^ (a - 1) * δ + T ^ (a - b) * C ^ b
        = ε ^ a / 2 + T ^ (a - b) * C ^ b := by rw [hmain]
    _ < ε ^ a / 2 + ε ^ a / 2 := add_lt_add_right htail_lt _
    _ = ε ^ a := by ring

/-- Helper for Theorem 8.16: a uniform `L^q` bound upgrades sufficiently small `L¹` norm to a
small strict-subcritical `Lᵖ` norm. -/
lemma subcriticalLpSmall_of_l1Small_and_uniformHighNorm
    {α : Type*}
    {_m : MeasurableSpace α}
    {μ : MeasureTheory.Measure α}
    {p q : ENNReal}
    (hp_one : 1 < p.toReal)
    (hpq : p.toReal < q.toReal)
    (hq_top : q ≠ (⊤ : ENNReal))
    {C : ℝ}
    (hC : 0 ≤ C) :
    ∀ ε > 0, ∃ δ > 0,
      ∀ ⦃w : α → ℝ⦄,
        MeasureTheory.MemLp w 1 μ →
        MeasureTheory.MemLp w q μ →
        MeasureTheory.eLpNorm w q μ ≤ ENNReal.ofReal C →
        (MeasureTheory.eLpNorm w 1 μ).toReal < δ →
        (MeasureTheory.eLpNorm w p μ).toReal < ε := by
  intro ε hε
  -- Route correction: choose the real threshold first, then keep the entire proof on the
  -- `eLpNormInterpolateOneHigh` surface instead of reopening `ENNReal.toReal` normalization.
  rcases interpolationThresholdChoice hp_one hpq hC hε with ⟨T, hT, δ, hδ, hchoice⟩
  refine ⟨δ, hδ, ?_⟩
  intro w hw1 hwq hwq_bound hw1_small
  have hq_toReal_le :
      (MeasureTheory.eLpNorm w q μ).toReal ≤ C := by
    -- The uniform `L^q` bound is stored as an `ℝ≥0∞` inequality, so convert it once to `ℝ`.
    exact ENNReal.toReal_le_of_le_ofReal hC hwq_bound
  have hq_toReal_rpow_le :
      (MeasureTheory.eLpNorm w q μ).toReal ^ q.toReal ≤ C ^ q.toReal := by
    -- Raise the converted `L^q` bound to the interpolation exponent.
    exact Real.rpow_le_rpow ENNReal.toReal_nonneg hq_toReal_le ENNReal.toReal_nonneg
  have hp_interp :=
    eLpNormInterpolateOneHigh
      (w := w) (p := p) (q := q) hw1 hwq hp_one hpq hq_top hT
  have hlow :
      T ^ (p.toReal - 1) * (MeasureTheory.eLpNorm w 1 μ).toReal <
        T ^ (p.toReal - 1) * δ := by
    -- The chosen `δ` makes the low-order term arbitrarily small.
    exact mul_lt_mul_of_pos_left hw1_small (by positivity)
  have hhigh :
      T ^ (p.toReal - q.toReal) * (MeasureTheory.eLpNorm w q μ).toReal ^ q.toReal ≤
        T ^ (p.toReal - q.toReal) * C ^ q.toReal := by
    -- The uniform `L^q` bound controls the high-order interpolation term.
    exact mul_le_mul_of_nonneg_left hq_toReal_rpow_le (by positivity)
  have hp_pow_lt :
      (MeasureTheory.eLpNorm w p μ).toReal ^ p.toReal < ε ^ p.toReal := by
    calc
      (MeasureTheory.eLpNorm w p μ).toReal ^ p.toReal ≤
          T ^ (p.toReal - 1) * (MeasureTheory.eLpNorm w 1 μ).toReal +
            T ^ (p.toReal - q.toReal) * (MeasureTheory.eLpNorm w q μ).toReal ^ q.toReal :=
        hp_interp
      _ < T ^ (p.toReal - 1) * δ + T ^ (p.toReal - q.toReal) * C ^ q.toReal :=
        add_lt_add_of_lt_of_le hlow hhigh
      _ < ε ^ p.toReal := hchoice
  by_contra hp_not_lt
  have hε_le : ε ≤ (MeasureTheory.eLpNorm w p μ).toReal := le_of_not_gt hp_not_lt
  have hε_pow_le :
      ε ^ p.toReal ≤ (MeasureTheory.eLpNorm w p μ).toReal ^ p.toReal := by
    -- Positive exponents preserve order on the nonnegative norm surface.
    have hp_nonneg : 0 ≤ p.toReal := by linarith
    exact Real.rpow_le_rpow hε.le hε_le hp_nonneg
  exact (not_lt_of_ge hε_pow_le) hp_pow_lt

/-- Helper for Theorem 8.16: the remaining strict-subcritical step is a uniform modulus turning
small `L¹(Ω)` differences on one BV closed ball into small `Lᵖ(Ω)` differences. -/
lemma subcriticalDifference_small_of_l1_small
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {p : ENNReal}
    [Fact (1 ≤ p)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hp : p < criticalExponent d)
    (R : ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ ⦃u v : BV Ω⦄,
      u ∈ Metric.closedBall (0 : BV Ω) R →
      v ∈ Metric.closedBall (0 : BV Ω) R →
      dist u.toL1 v.toL1 < δ →
      dist (toSubcriticalLp (d := d) (Ω := Ω) (p := p) hd hΩ hp u)
        (toSubcriticalLp (d := d) (Ω := Ω) (p := p) hd hΩ hp v) < ε := by
  intro ε hε
  by_cases hp1 : p = 1
  · subst hp1
    refine ⟨ε, hε, ?_⟩
    intro u v hu hv huv
    have hu_eq :
        toSubcriticalLp (d := d) (Ω := Ω) (p := (1 : ENNReal)) hd hΩ hp u = u.toL1 := by
      -- At exponent `1`, the strict-subcritical embedding is exactly the canonical `L¹` point.
      apply Subtype.ext
      simpa using toSubcriticalLp_toAEEqFun (d := d) (Ω := Ω) (p := (1 : ENNReal)) hd hΩ hp u
    have hv_eq :
        toSubcriticalLp (d := d) (Ω := Ω) (p := (1 : ENNReal)) hd hΩ hp v = v.toL1 := by
      -- The same identification holds for the second BV point.
      apply Subtype.ext
      simpa using toSubcriticalLp_toAEEqFun (d := d) (Ω := Ω) (p := (1 : ENNReal)) hd hΩ hp v
    -- After identifying both strict-subcritical points with their `L¹` representatives, the
    -- desired estimate is exactly the assumed `L¹` closeness.
    simpa [hu_eq, hv_eq] using huv
  · -- Route correction: the remaining frontier is the genuine interpolation estimate for `1 < p`,
    -- split further into the one-dimensional endpoint and the finite-critical `1 < d` branch.
    by_cases hd1 : d = 1
    · subst hd1
      exact
        subcriticalDifference_small_of_l1_small_endpoint
          (Ω := Ω) (p := p) hΩ hp R ε hε
    · -- Route correction: normalize both distances to the shared BV-difference representative, then
      -- apply the file-local `L¹`/`L^q` interpolation modulus at `q = criticalExponent d`.
      have h1d : 1 < d := lt_of_le_of_ne hd (by simpa [eq_comm] using hd1)
      have hqcrit_top : criticalExponent d ≠ (⊤ : ENNReal) := by
        rw [criticalExponent_eq_div_of_ne_one (d := d) hd1]
        exact ENNReal.div_ne_top ENNReal.coe_ne_top (by exact_mod_cast Nat.sub_ne_zero_of_lt h1d)
      have hp_top : p ≠ (⊤ : ENNReal) := by
        intro hp_top
        exact (not_lt_of_ge (hp_top ▸ le_top)).elim hp
      have hp_toReal_gt_one : 1 < p.toReal := by
        exact
          (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2
            (lt_of_le_of_ne Fact.out (by simpa [eq_comm] using hp1))
      have hp_toReal_lt_crit :
          p.toReal < (criticalExponent d).toReal := by
        exact (ENNReal.toReal_lt_toReal hp_top hqcrit_top).2 hp
      rcases subcriticalDifference_uniformCriticalBound (d := d) (Ω := Ω) h1d hΩ R with
        ⟨C, hC, hCball⟩
      rcases
          subcriticalLpSmall_of_l1Small_and_uniformHighNorm
            (p := p)
            (q := criticalExponent d)
            hp_toReal_gt_one
            hp_toReal_lt_crit
            hqcrit_top
            hC
            ε hε with
        ⟨δ, hδ, hδprop⟩
      refine ⟨δ, hδ, ?_⟩
      intro u v hu hv huv
      let w : (EuclideanSpace ℝ (Fin d)) → ℝ :=
        fun x ↦
          ((((u - v).toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
            (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ) x)
      have hw1 : MeasureTheory.MemLp w 1 (domainMeasure Ω) := by
        simpa [w] using MeasureTheory.Lp.memLp ((u - v).toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω))
      have hwq :
          MeasureTheory.MemLp w (criticalExponent d) (domainMeasure Ω) := by
        refine ⟨?_, ?_⟩
        · simpa [w] using
            (MeasureTheory.Lp.memLp ((u - v).toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω))).aestronglyMeasurable
        · exact lt_of_le_of_lt (hCball hu hv) ENNReal.ofReal_lt_top
      rcases
          subcriticalDifference_dist_eq_eLpNorm
            (d := d) (Ω := Ω) (p := p) hd hΩ hp u v with
        ⟨hdistp, hdist1⟩
      have huv' :
          (MeasureTheory.eLpNorm w 1 (domainMeasure Ω)).toReal < δ := by
        simpa [w, hdist1] using huv
      have hdistp' :
          (MeasureTheory.eLpNorm w p (domainMeasure Ω)).toReal < ε :=
        hδprop hw1 hwq (by simpa [w] using hCball hu hv) huv'
      simpa [w, hdistp] using hdistp'

/-- Helper for Theorem 8.16: the strict-subcritical image of a BV closed ball is compact once the
theorem-local `BV → Lᵖ` embedding owner is upgraded to a quantitative compactness statement. -/
lemma subcriticalClosedBall_totallyBounded
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {p : ENNReal}
    [Fact (1 ≤ p)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hp : p < criticalExponent d)
    (R : ℝ) :
    TotallyBounded (subcriticalLpImage hd hΩ hp (Metric.closedBall (0 : BV Ω) R)) := by
  change
    TotallyBounded
      (toLp (d := d) (Ω := Ω) (p := p) hd hΩ (le_of_lt hp) ''
        Metric.closedBall (0 : BV Ω) R)
  by_cases hR : R < 0
  · -- A negative-radius BV closed ball is empty, so its strict-subcritical image is totally
    -- bounded for the trivial reason that the image itself is empty.
    simpa [Metric.closedBall_eq_empty.2 hR]
  · -- Route correction: once the local `L¹ → Lᵖ` modulus is available, total boundedness follows
    -- from the abstract cover-transfer lemma applied to the canonical `BV.toL1` image.
    refine
      totallyBounded_image_of_controlled
        (s := Metric.closedBall (0 : BV Ω) R)
        (g := fun u : BV Ω ↦ u.toL1)
        (f := toLp (d := d) (Ω := Ω) (p := p) hd hΩ (le_of_lt hp))
        ?_ ?_
    · -- The `L¹` image of the same BV closed ball is already totally bounded.
      simpa using toL1ClosedBall_totallyBounded (d := d) (Ω := Ω) hΩ R
    · -- The only remaining analytic input is the strict-subcritical `L¹ → Lᵖ` modulus.
      intro ε hε
      rcases
          subcriticalDifference_small_of_l1_small
            (d := d) (Ω := Ω) (p := p) hd hΩ hp R ε hε with
        ⟨δ, hδ, hδprop⟩
      refine ⟨δ, hδ, ?_⟩
      intro u v hu hv huv
      have hu_toLp :
          toLp (d := d) (Ω := Ω) (p := p) hd hΩ (le_of_lt hp) u =
            toSubcriticalLp (d := d) (Ω := Ω) (p := p) hd hΩ hp u :=
        toLp_eq_toSubcriticalLp (d := d) (Ω := Ω) (p := p) hd hΩ hp u
      have hv_toLp :
          toLp (d := d) (Ω := Ω) (p := p) hd hΩ (le_of_lt hp) v =
            toSubcriticalLp (d := d) (Ω := Ω) (p := p) hd hΩ hp v :=
        toLp_eq_toSubcriticalLp (d := d) (Ω := Ω) (p := p) hd hΩ hp v
      simpa [hu_toLp, hv_toLp] using hδprop hu hv huv

/-- Helper for Theorem 8.16: the strict-subcritical image of a BV closed ball is compact once the
theorem-local `BV → Lᵖ` embedding owner is upgraded to a quantitative compactness statement. -/
lemma subcriticalClosedBall_compact
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {p : ENNReal}
    [Fact (1 ≤ p)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hp : p < criticalExponent d)
    (R : ℝ) :
    IsCompact (closure (subcriticalLpImage hd hΩ hp (Metric.closedBall (0 : BV Ω) R))) := by
  -- Route correction: the theorem-local total-boundedness transfer is the only remaining analytic
  -- step, so the compactness statement itself is now a standard closure wrapper.
  exact
    isCompact_closure_of_totallyBounded_quasiComplete
      (𝕜 := ℝ)
      (s := subcriticalLpImage hd hΩ hp (Metric.closedBall (0 : BV Ω) R))
      (subcriticalClosedBall_totallyBounded (d := d) (Ω := Ω) (p := p) hd hΩ hp R)

/-- Helper for Theorem 8.16: the critical weak image of a BV closed ball is compact once the
closed-ball weak compactness owner is supplied on the canonical critical `Lᵖ` surface. -/
lemma criticalWeakImage_subset_toWeakSpace_closedBall_of_exactBound
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (h1d : 1 < d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (R : ℝ) :
    ∃ C : ℝ,
      0 ≤ C ∧
      criticalWeakImage h1d hΩ (Metric.closedBall (0 : BV Ω) R) ⊆
        toWeakSpace ℝ (criticalLpSpace Ω (Nat.le_of_lt h1d)) ''
          Metric.closedBall (0 : criticalLpSpace Ω (Nat.le_of_lt h1d)) C := by
  -- Route correction: isolate the easy quantitative consequence of the exact critical bound before
  -- attacking weak compactness of the closure.
  rcases criticalClosedBall_exactBound (d := d) (Ω := Ω) h1d hΩ R with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro z hz
  rcases hz with ⟨y, hy, rfl⟩
  rcases hy with ⟨u, hu, rfl⟩
  refine ⟨toCriticalLp (d := d) (Ω := Ω) (Nat.le_of_lt h1d) hΩ u, ?_, rfl⟩
  -- Unfold the canonical `Lp` packaging once so the exact critical `eLpNorm` estimate becomes a
  -- closed-ball norm bound.
  rw [Metric.mem_closedBall, dist_zero_right]
  have htoCritical_fun :
      ((toCriticalLp (d := d) (Ω := Ω) (Nat.le_of_lt h1d) hΩ u :
          criticalLpSpace Ω (Nat.le_of_lt h1d)) :
          EuclideanSpace ℝ (Fin d) → ℝ) =
        (u.toL1 : EuclideanSpace ℝ (Fin d) → ℝ) := by
    -- The critical-space representative and the canonical `L¹` representative are the same
    -- function once we forget the `Lp` packaging.
    exact
      congrArg
        (fun z : (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ =>
          (z : EuclideanSpace ℝ (Fin d) → ℝ))
        (toCriticalLp_toAEEqFun (d := d) (Ω := Ω) (Nat.le_of_lt h1d) hΩ u)
  have hnorm :
      ‖toCriticalLp (d := d) (Ω := Ω) (Nat.le_of_lt h1d) hΩ u‖ =
        ENNReal.toReal
          (MeasureTheory.eLpNorm u.toL1 (criticalExponent d) (domainMeasure Ω)) := by
    -- Rewrite the `Lp` norm through the pointwise representative supplied by
    -- `toCriticalLp_toAEEqFun`.
    rw [MeasureTheory.Lp.norm_def]
    refine congrArg ENNReal.toReal ?_
    apply MeasureTheory.eLpNorm_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by simpa using congrFun htoCritical_fun x
  rw [hnorm]
  exact ENNReal.toReal_le_of_le_ofReal hC_nonneg (hC hu)

/-- Helper for Theorem 8.16: the exact critical closed-ball bound already makes the pulled-back
critical weak image bounded in the norm topology of `criticalLpSpace Ω`. -/
lemma criticalWeakImage_preimage_bounded_of_exactBound
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (h1d : 1 < d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (R : ℝ) :
    Bornology.IsBounded
      (((toWeakSpace ℝ (criticalLpSpace Ω (Nat.le_of_lt h1d))) ⁻¹'
        criticalWeakImage h1d hΩ (Metric.closedBall (0 : BV Ω) R)) : Set
          (criticalLpSpace Ω (Nat.le_of_lt h1d))) := by
  -- First place the weak image inside the weak-topology image of one norm closed ball.
  rcases
      criticalWeakImage_subset_toWeakSpace_closedBall_of_exactBound
        (d := d) (Ω := Ω) h1d hΩ R with
    ⟨C, _hC_nonneg, hsubset⟩
  have hbounded_preimage_image :
      Bornology.IsBounded
        (((toWeakSpace ℝ (criticalLpSpace Ω (Nat.le_of_lt h1d))) ⁻¹'
          (toWeakSpace ℝ (criticalLpSpace Ω (Nat.le_of_lt h1d)) ''
            Metric.closedBall (0 : criticalLpSpace Ω (Nat.le_of_lt h1d)) C)) : Set
            (criticalLpSpace Ω (Nat.le_of_lt h1d))) := by
    -- Pulling back the `toWeakSpace` image simply recovers the original norm closed ball.
    have hpreimage_subset :
        (((toWeakSpace ℝ (criticalLpSpace Ω (Nat.le_of_lt h1d))) ⁻¹'
          (toWeakSpace ℝ (criticalLpSpace Ω (Nat.le_of_lt h1d)) ''
            Metric.closedBall (0 : criticalLpSpace Ω (Nat.le_of_lt h1d)) C)) : Set
            (criticalLpSpace Ω (Nat.le_of_lt h1d))) ⊆
          Metric.closedBall (0 : criticalLpSpace Ω (Nat.le_of_lt h1d)) C := by
      intro x hx
      rcases hx with ⟨y, hy, hxy⟩
      exact (toWeakSpace ℝ (criticalLpSpace Ω (Nat.le_of_lt h1d))).injective hxy ▸ hy
    exact Metric.isBounded_closedBall.subset hpreimage_subset
  -- Then restrict from that preimage to the actual critical weak image.
  refine hbounded_preimage_image.subset ?_
  intro x hx
  exact hsubset hx

lemma criticalClosedBall_weakCompact
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (h1d : 1 < d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (R : ℝ) :
    IsCompact
      (closure
        (criticalWeakImage h1d hΩ (Metric.closedBall (0 : BV Ω) R))) := by
  rcases
      criticalWeakImage_subset_toWeakSpace_closedBall_of_exactBound
        (d := d) (Ω := Ω) h1d hΩ R with
    ⟨C, _hC_nonneg, hsubset⟩
  -- The exact critical bound places the weak image inside one weak closed ball, so the canonical
  -- support owner closes the compactness argument directly.
  exact
    (criticalLpClosedBall_weakCompact (d := d) (Ω := Ω) h1d C).of_isClosed_subset
      isClosed_closure (closure_mono hsubset)

/-- Theorem 8.16 (1). Under the standing finite-measure hypothesis on
`domainMeasure Ω`, a BV-bounded family on bounded `Ω` is relatively compact in
`Lᵖ(Ω)` for every exponent `p` with `1 ≤ p < criticalExponent d`. -/
theorem subcriticalLp
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {p : ENNReal}
    [Fact (1 ≤ p)]
    (hd : 1 ≤ d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (S : Set (BV Ω))
    (hS : IsBVBounded (BV.toL1 '' S))
    (hp : p < criticalExponent d) :
    IsCompact (closure (subcriticalLpImage hd hΩ hp S)) := by
  -- Route correction: reduce the BV-bounded family to one BV closed ball, then use the owner-side
  -- monotonicity bridge instead of unfolding the imported image surface in place.
  rcases subset_closedBall_of_isBVBounded S hS with ⟨R, hR⟩
  have hmono :
      subcriticalLpImage hd hΩ hp S ⊆
        subcriticalLpImage hd hΩ hp (Metric.closedBall (0 : BV Ω) R) := by
    -- Consume the exposed strict-subcritical monotonicity theorem directly.
    exact subcriticalLpImage_mono (d := d) (Ω := Ω) (p := p) hd hΩ hp hR
  -- The closure of the smaller image is a closed subset of the compact closed-ball image.
  exact
    (subcriticalClosedBall_compact (d := d) (Ω := Ω) (p := p) hd hΩ hp R).of_isClosed_subset
      isClosed_closure (closure_mono hmono)

/-- Theorem 8.16 (2). Under the standing finite-measure hypothesis on
`domainMeasure Ω`, if `1 < d` then a BV-bounded family on bounded `Ω` is weakly
relatively compact in `L^(criticalExponent d)(Ω)`. -/
theorem criticalWeakLp
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (h1d : 1 < d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (S : Set (BV Ω))
    (hS : IsBVBounded (BV.toL1 '' S)) :
    IsCompact (closure (criticalWeakImage h1d hΩ S)) := by
  -- Route correction: the critical clause uses the same closed-ball reduction, now on the
  -- canonical weak image surface exposed by the owner file.
  rcases subset_closedBall_of_isBVBounded S hS with ⟨R, hR⟩
  have hmono :
      criticalWeakImage h1d hΩ S ⊆
        criticalWeakImage h1d hΩ (Metric.closedBall (0 : BV Ω) R) := by
    -- Route correction: consume the exposed weak-image monotonicity theorem directly.
    exact criticalWeakImage_mono (d := d) (Ω := Ω) h1d hΩ hR
  -- Compactness of the closed-ball image transfers to the closed subset cut out by `S`.
  exact
    (criticalClosedBall_weakCompact (d := d) (Ω := Ω) h1d hΩ R).of_isClosed_subset
      isClosed_closure (closure_mono hmono)

end GeneralDimension

section OneDimensional

variable {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1))}

/-- Helper for Theorem 8.16: a uniform strong-dual norm bound on the endpoint representatives puts
the weak-* image inside one weak-* closed ball. -/
lemma endpointWeakStarImage_subset_closedBall_of_dualBound
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 1))))
    {S : Set (BV Ω)}
    {R : ℝ}
    (hR :
      ∀ ⦃u : BV Ω⦄, u ∈ S →
        ‖(endpointWeakStarOfLp (toEndpointLp hΩ u)).toStrongDual‖ ≤ R) :
    endpointWeakStarImage hΩ S ⊆
      WeakDual.toStrongDual ⁻¹'
        Metric.closedBall
          (0 : StrongDual ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))) R := by
  intro z hz
  rcases hz with ⟨w, hw, rfl⟩
  rcases hw with ⟨u, hu, rfl⟩
  -- The chosen endpoint witness already satisfies the advertised strong-dual norm bound.
  simpa [Metric.mem_closedBall, dist_zero_right] using hR hu

/-- Helper for Theorem 8.16: Banach-Alaoglu makes any endpoint weak-* image compact once it is
contained in a single weak-* closed ball. -/
lemma endpointWeakStarImage_compact_of_subset_closedBall
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 1))))
    {S : Set (BV Ω)}
    {R : ℝ}
    (hsubset :
      endpointWeakStarImage hΩ S ⊆
        WeakDual.toStrongDual ⁻¹'
          Metric.closedBall
            (0 : StrongDual ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))) R) :
    IsCompact (closure (endpointWeakStarImage hΩ S)) := by
  -- Banach-Alaoglu gives compactness of the ambient weak-* closed ball.
  exact
    (WeakDual.isCompact_closedBall
        (𝕜 := ℝ)
        (E := MeasureTheory.Lp ℝ 1 (domainMeasure Ω))
        (0 : StrongDual ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))) R).of_isClosed_subset
      isClosed_closure
      (closure_minimal hsubset
        (WeakDual.isClosed_closedBall
          (𝕜 := ℝ)
          (E := MeasureTheory.Lp ℝ 1 (domainMeasure Ω))
          (0 : StrongDual ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))) R))

/-- Helper for Theorem 8.16: the canonical `L∞(Ω)` endpoint pairing defines a strong-dual element
with norm controlled by the `L∞` norm of the representative. -/
lemma endpointWeakStarOfLp_toStrongDual_norm_le
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (f : MeasureTheory.Lp ℝ ⊤ (domainMeasure Ω)) :
    ‖(endpointWeakStarOfLp f).toStrongDual‖ ≤ ‖f‖ := by
  -- Remove the weak-dual wrapper so the goal becomes an operator-norm bound for the pairing map.
  have htoStrong :
      (endpointWeakStarOfLp f).toStrongDual =
        ((ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure Ω) (⊤ : ENNReal) (1 : ENNReal) f) := by
    ext g
    -- Both sides evaluate by the same `L∞`-`L¹` pairing formula.
    rw [WeakDual.toStrongDual_apply, endpointWeakStarOfLp_apply]
  rw [htoStrong]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
  intro g
  calc
    ‖((ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure Ω) (⊤ : ENNReal) (1 : ENNReal) f) g‖
      = ‖MeasureTheory.L1.integralCLM
          (α := EuclideanSpace ℝ (Fin 1)) (E := ℝ) (μ := domainMeasure Ω)
          ((ContinuousLinearMap.mul ℝ ℝ).holder
            (μ := domainMeasure Ω) (p := (⊤ : ENNReal)) (q := (1 : ENNReal))
            (r := (1 : ENNReal)) f g)‖ := by
          rfl
    _ ≤ ‖(ContinuousLinearMap.mul ℝ ℝ).holder
          (μ := domainMeasure Ω) (p := (⊤ : ENNReal)) (q := (1 : ENNReal))
          (r := (1 : ENNReal)) f g‖ := by
          exact
            (ContinuousLinearMap.le_opNorm
              (MeasureTheory.L1.integralCLM
                (α := EuclideanSpace ℝ (Fin 1)) (E := ℝ) (μ := domainMeasure Ω))
              _).trans <| by
                simpa using
                  (mul_le_mul_of_nonneg_right MeasureTheory.L1.norm_Integral_le_one
                    (norm_nonneg _))
    _ ≤ ‖(ContinuousLinearMap.mul ℝ ℝ)‖ * ‖f‖ * ‖g‖ := by
          simpa using
            (ContinuousLinearMap.norm_holder_apply_apply_le
              (B := ContinuousLinearMap.mul ℝ ℝ) (r := (1 : ENNReal)) f g)
    _ ≤ 1 * ‖f‖ * ‖g‖ := by
          gcongr
          simpa using (ContinuousLinearMap.opNorm_mul_le (𝕜 := ℝ) (R := ℝ))
    _ = ‖f‖ * ‖g‖ := by ring

/-- Helper for Theorem 8.16: the one-dimensional endpoint BV closed ball has a uniform strong-dual
norm bound once the quantitative `L∞` owner is available. -/
lemma endpointClosedBall_dualBound
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 1))))
    (R : ℝ) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ ⦃u : BV Ω⦄, u ∈ Metric.closedBall (0 : BV Ω) R →
        ‖(endpointWeakStarOfLp (toEndpointLp hΩ u)).toStrongDual‖ ≤ C := by
  -- Reuse the quantitative endpoint a.e. bound, then pass it through the canonical `L∞` pairing.
  rcases endpointClosedBall_aeBound (Ω := Ω) hΩ R with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro u hu
  have htoEndpoint_fun :
      ((toEndpointLp (Ω := Ω) hΩ u : MeasureTheory.Lp ℝ ⊤ (domainMeasure Ω)) :
          EuclideanSpace ℝ (Fin 1) → ℝ) =
        (u.toL1 : EuclideanSpace ℝ (Fin 1) → ℝ) := by
    exact
      congrArg
        (fun z : (EuclideanSpace ℝ (Fin 1)) →ₘ[domainMeasure Ω] ℝ =>
          (z : EuclideanSpace ℝ (Fin 1) → ℝ))
        (toEndpointLp_toAEEqFun (Ω := Ω) hΩ u)
  have htoEndpoint_ae :
      ((toEndpointLp (Ω := Ω) hΩ u : MeasureTheory.Lp ℝ ⊤ (domainMeasure Ω)) :
          EuclideanSpace ℝ (Fin 1) → ℝ) =ᵐ[domainMeasure Ω] u.toL1 := by
    -- The exposed `AEEqFun` bridge identifies the endpoint representative with `u.toL1`.
    exact Filter.Eventually.of_forall fun x ↦ by simpa using congrFun htoEndpoint_fun x
  have hnorm_endpoint : ‖toEndpointLp (Ω := Ω) hΩ u‖ ≤ C := by
    -- Transfer the a.e. pointwise bound from `u.toL1` to the packaged endpoint representative.
    have hnorm_endpoint' :=
      MeasureTheory.Lp.norm_le_of_ae_bound
        (f := toEndpointLp (Ω := Ω) hΩ u) hC_nonneg ?_
    · simpa using hnorm_endpoint'
    filter_upwards [htoEndpoint_ae, hC hu] with x hx_eq hx_bound
    simpa [hx_eq] using hx_bound
  -- The strong-dual norm is dominated by the endpoint `L∞` norm.
  exact (endpointWeakStarOfLp_toStrongDual_norm_le (Ω := Ω) (toEndpointLp hΩ u)).trans hnorm_endpoint

/-- Helper for Theorem 8.16: the one-dimensional weak-* image of a BV closed ball is compact once
the endpoint pairing map is shown to land in a weak-* closed ball. -/
lemma endpointClosedBall_weakStarCompact
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 1))))
    (R : ℝ) :
    IsCompact
      (closure
        (endpointWeakStarImage hΩ (Metric.closedBall (0 : BV Ω) R))) := by
  -- Route correction: the Banach-Alaoglu step now only consumes the closed-ball dual bound, which
  -- is packaged separately from the endpoint compactness endgame.
  rcases endpointClosedBall_dualBound (Ω := Ω) hΩ R with ⟨C, _, hC⟩
  refine endpointWeakStarImage_compact_of_subset_closedBall (Ω := Ω) (R := C) hΩ ?_
  refine endpointWeakStarImage_subset_closedBall_of_dualBound (Ω := Ω) (R := C) hΩ ?_
  intro u hu
  exact hC hu

/-- Theorem 8.16 (3). When `d = 1`, the source convention
`d / (d - 1) = ∞` yields weak-* relative compactness in `L∞(Ω)` for a
BV-bounded family on bounded `Ω`, expressed on the canonical `L¹(Ω)` predual
surface. -/
theorem endpointWeakStarLp
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 1))))
    (S : Set (BV Ω))
    (hS : IsBVBounded (BV.toL1 '' S)) :
    IsCompact (closure (endpointWeakStarImage hΩ S)) := by
  -- Route correction: the one-dimensional endpoint also reduces to one BV closed ball and then
  -- uses the owner-side monotonicity theorem on the weak-* image surface.
  rcases subset_closedBall_of_isBVBounded S hS with ⟨R, hR⟩
  have hmono :
      endpointWeakStarImage hΩ S ⊆
        endpointWeakStarImage hΩ (Metric.closedBall (0 : BV Ω) R) := by
    -- Route correction: the endpoint surface already exposes the required monotonicity theorem.
    exact endpointWeakStarImage_mono (Ω := Ω) hΩ hR
  -- The endpoint closed-ball compactness owner finishes the weak-* compactness claim.
  exact
    (endpointClosedBall_weakStarCompact (Ω := Ω) hΩ R).of_isClosed_subset
      isClosed_closure (closure_mono hmono)

end OneDimensional

end BVCompactness

end VariationalRegularization
