/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Example 7.13: scaling both coordinates by the same nonnegative factor pulls that
factor out of the weighted geometric mean. -/
private lemma weightedGeometricMean_scale {α c x y : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (c * x).rpow α * (c * y).rpow (1 - α) = c * (x.rpow α * y.rpow (1 - α)) := by
  have h1α0 : 0 ≤ 1 - α := sub_nonneg.2 hα1
  have hmulx : (c * x).rpow α = c.rpow α * x.rpow α := by
    simpa using (Real.mul_rpow hc hx (z := α))
  have hmuly : (c * y).rpow (1 - α) = c.rpow (1 - α) * y.rpow (1 - α) := by
    simpa using (Real.mul_rpow hc hy (z := 1 - α))
  have hmulc : c.rpow α * c.rpow (1 - α) = c := by
    calc
      c.rpow α * c.rpow (1 - α) = c.rpow (α + (1 - α)) := by
        simpa [Real.rpow_eq_pow] using (Real.rpow_add_of_nonneg hc hα0 h1α0).symm
      _ = c.rpow (1 : ℝ) := by rw [add_sub_cancel]
      _ = c := by simp [Real.rpow_eq_pow]
  -- Rewrite the common factor `c` through each `rpow`, then recombine the exponents on `c`.
  calc
    (c * x).rpow α * (c * y).rpow (1 - α)
        = (c.rpow α * x.rpow α) * (c.rpow (1 - α) * y.rpow (1 - α)) := by
            rw [hmulx, hmuly]
    _ = (c.rpow α * c.rpow (1 - α)) * (x.rpow α * y.rpow (1 - α)) := by ring
    _ = c * (x.rpow α * y.rpow (1 - α)) := by rw [hmulc]

/-- Helper for Example 7.13: Hölder's inequality for two points yields the concavity inequality for
the weighted geometric mean on the nonnegative quadrant. -/
private lemma sum_weightedGeometricMean_le_weightedGeometricMean_sum {α a b x₁ x₂ y₁ y₂ : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hx₁ : 0 ≤ x₁)
    (hx₂ : 0 ≤ x₂) (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) :
    a * x₁.rpow α * x₂.rpow (1 - α) + b * y₁.rpow α * y₂.rpow (1 - α) ≤
      (a * x₁ + b * y₁).rpow α * (a * x₂ + b * y₂).rpow (1 - α) := by
  have hα0' : 0 ≤ α := hα0.le
  have h1α0 : 0 < 1 - α := sub_pos.2 hα1
  have h1α0' : 0 ≤ 1 - α := h1α0.le
  have hpq : (1 / α).HolderConjugate (1 / (1 - α)) := by
    exact Real.holderConjugate_one_div hα0 h1α0 (by linarith)
  have hα_ne : α ≠ 0 := hα0.ne'
  have h1α_ne : 1 - α ≠ 0 := h1α0.ne'
  let f : Fin 2 → ℝ
    | 0 => (a * x₁).rpow α
    | 1 => (b * y₁).rpow α
  let g : Fin 2 → ℝ
    | 0 => (a * x₂).rpow (1 - α)
    | 1 => (b * y₂).rpow (1 - α)
  have hf_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ f i := by
    intro i hi
    fin_cases i
    · simpa [f] using Real.rpow_nonneg (mul_nonneg ha hx₁) α
    · simpa [f] using Real.rpow_nonneg (mul_nonneg hb hy₁) α
  have hg_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ g i := by
    intro i hi
    fin_cases i
    · simpa [g] using Real.rpow_nonneg (mul_nonneg ha hx₂) (1 - α)
    · simpa [g] using Real.rpow_nonneg (mul_nonneg hb hy₂) (1 - α)
  have hf0 :
      ((a * x₁).rpow α).rpow (1 / α) = a * x₁ := by
    have hm :
        ((a * x₁).rpow α).rpow (1 / α) = (a * x₁).rpow (α * (1 / α)) := by
      simpa using (Real.rpow_mul (mul_nonneg ha hx₁) α (1 / α)).symm
    rw [hm]
    have : α * (1 / α) = 1 := by field_simp [hα_ne]
    rw [this]
    simp [Real.rpow_eq_pow]
  have hf1 :
      ((b * y₁).rpow α).rpow (1 / α) = b * y₁ := by
    have hm :
        ((b * y₁).rpow α).rpow (1 / α) = (b * y₁).rpow (α * (1 / α)) := by
      simpa using (Real.rpow_mul (mul_nonneg hb hy₁) α (1 / α)).symm
    rw [hm]
    have : α * (1 / α) = 1 := by field_simp [hα_ne]
    rw [this]
    simp [Real.rpow_eq_pow]
  have hg0 :
      ((a * x₂).rpow (1 - α)).rpow (1 / (1 - α)) = a * x₂ := by
    have hm :
        ((a * x₂).rpow (1 - α)).rpow (1 / (1 - α)) =
          (a * x₂).rpow ((1 - α) * (1 / (1 - α))) := by
      simpa using (Real.rpow_mul (mul_nonneg ha hx₂) (1 - α) (1 / (1 - α))).symm
    rw [hm]
    have : (1 - α) * (1 / (1 - α)) = 1 := by field_simp [h1α_ne]
    rw [this]
    simp [Real.rpow_eq_pow]
  have hg1 :
      ((b * y₂).rpow (1 - α)).rpow (1 / (1 - α)) = b * y₂ := by
    have hm :
        ((b * y₂).rpow (1 - α)).rpow (1 / (1 - α)) =
          (b * y₂).rpow ((1 - α) * (1 / (1 - α))) := by
      simpa using (Real.rpow_mul (mul_nonneg hb hy₂) (1 - α) (1 / (1 - α))).symm
    rw [hm]
    have : (1 - α) * (1 / (1 - α)) = 1 := by field_simp [h1α_ne]
    rw [this]
    simp [Real.rpow_eq_pow]
  have hsum_f :
      ∑ i ∈ (Finset.univ : Finset (Fin 2)), (f i).rpow (1 / α) = a * x₁ + b * y₁ := by
    calc
      ∑ i ∈ (Finset.univ : Finset (Fin 2)), (f i).rpow (1 / α)
          = ((a * x₁).rpow α).rpow (1 / α) + ((b * y₁).rpow α).rpow (1 / α) := by
              simp [f]
      _ = a * x₁ + b * y₁ := by rw [hf0, hf1]
  have hsum_g :
      ∑ i ∈ (Finset.univ : Finset (Fin 2)), (g i).rpow (1 / (1 - α)) = a * x₂ + b * y₂ := by
    calc
      ∑ i ∈ (Finset.univ : Finset (Fin 2)), (g i).rpow (1 / (1 - α))
          = ((a * x₂).rpow (1 - α)).rpow (1 / (1 - α)) +
              ((b * y₂).rpow (1 - α)).rpow (1 / (1 - α)) := by
                simp [g]
      _ = a * x₂ + b * y₂ := by rw [hg0, hg1]
  have hleft :
      ∑ i ∈ (Finset.univ : Finset (Fin 2)), f i * g i
        = a * x₁.rpow α * x₂.rpow (1 - α) + b * y₁.rpow α * y₂.rpow (1 - α) := by
    calc
      ∑ i ∈ (Finset.univ : Finset (Fin 2)), f i * g i
          = (a * x₁).rpow α * (a * x₂).rpow (1 - α) +
              (b * y₁).rpow α * (b * y₂).rpow (1 - α) := by
                simp [f, g]
      _ = a * (x₁.rpow α * x₂.rpow (1 - α)) +
            b * (y₁.rpow α * y₂.rpow (1 - α)) := by
              rw [weightedGeometricMean_scale ha hx₁ hx₂ hα0' hα1.le,
                weightedGeometricMean_scale hb hy₁ hy₂ hα0' hα1.le]
      _ = a * x₁.rpow α * x₂.rpow (1 - α) + b * y₁.rpow α * y₂.rpow (1 - α) := by ring
  have hHolder :=
    Real.inner_le_Lp_mul_Lq_of_nonneg (s := (Finset.univ : Finset (Fin 2))) hpq hf_nonneg hg_nonneg
  -- Rewrite Hölder's inequality into the exact two-point concavity inequality.
  have hpinv : 1 / (1 / α) = α := by field_simp [hα_ne]
  have hqinv : 1 / (1 / (1 - α)) = 1 - α := by field_simp [h1α_ne]
  calc
    a * x₁.rpow α * x₂.rpow (1 - α) + b * y₁.rpow α * y₂.rpow (1 - α)
        = ∑ i ∈ (Finset.univ : Finset (Fin 2)), f i * g i := by rw [← hleft]
    _ ≤ (∑ i ∈ (Finset.univ : Finset (Fin 2)), (f i).rpow (1 / α)) ^ (1 / (1 / α)) *
          (∑ i ∈ (Finset.univ : Finset (Fin 2)), (g i).rpow (1 / (1 - α))) ^
            (1 / (1 / (1 - α))) := hHolder
    _ = (a * x₁ + b * y₁).rpow α * (a * x₂ + b * y₂).rpow (1 - α) := by
          rw [hsum_f, hsum_g, hpinv, hqinv]
          simp [Real.rpow_eq_pow]

/-- Helper for Example 7.13: weighted AM-GM gives an integrable domination for the weighted
geometric mean of two nonnegative integrable random variables. -/
private lemma integrable_weightedGeometricMean {P : Measure Ω} {α : ℝ} {X Y : Ω → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hX : Integrable X P) (hY : Integrable Y P)
    (hX_nonneg : 0 ≤ᵐ[P] X) (hY_nonneg : 0 ≤ᵐ[P] Y) :
    Integrable (fun ω ↦ (X ω).rpow α * (Y ω).rpow (1 - α)) P := by
  have h1α0 : 0 ≤ 1 - α := sub_nonneg.2 hα1
  have hdom :
      ∀ᵐ ω ∂P, (X ω).rpow α * (Y ω).rpow (1 - α) ≤ α * X ω + (1 - α) * Y ω := by
    filter_upwards [hX_nonneg, hY_nonneg] with ω hXω hYω
    exact Real.geom_mean_le_arith_mean2_weighted hα0 h1α0 hXω hYω (by linarith)
  have hnonneg :
      ∀ᵐ ω ∂P, 0 ≤ (X ω).rpow α * (Y ω).rpow (1 - α) := by
    filter_upwards [hX_nonneg, hY_nonneg] with ω hXω hYω
    exact mul_nonneg (Real.rpow_nonneg hXω _) (Real.rpow_nonneg hYω _)
  have hsum_int :
      Integrable (fun ω ↦ α * X ω + (1 - α) * Y ω) P :=
    (hX.const_mul α).add (hY.const_mul (1 - α))
  have hX_rpow :
      AEStronglyMeasurable (fun ω ↦ (X ω).rpow α) P :=
    (Real.continuous_rpow_const hα0).comp_aestronglyMeasurable hX.aestronglyMeasurable
  have hY_rpow :
      AEStronglyMeasurable (fun ω ↦ (Y ω).rpow (1 - α)) P :=
    (Real.continuous_rpow_const h1α0).comp_aestronglyMeasurable hY.aestronglyMeasurable
  -- The weighted geometric mean is nonnegative, so the pointwise AM-GM bound also bounds its norm.
  refine Integrable.mono' hsum_int ?_ ?_
  · exact hX_rpow.mul hY_rpow
  · filter_upwards [hdom, hnonneg, hX_nonneg, hY_nonneg] with ω hω hω_nonneg hXω hYω
    have hXω_nonneg : 0 ≤ (X ω).rpow α := Real.rpow_nonneg hXω α
    have hYω_nonneg : 0 ≤ (Y ω).rpow (1 - α) := Real.rpow_nonneg hYω (1 - α)
    calc
      ‖(X ω).rpow α * (Y ω).rpow (1 - α)‖
          = |(X ω).rpow α| * |(Y ω).rpow (1 - α)| := by
              rw [Real.norm_eq_abs, abs_mul]
      _ = (X ω).rpow α * (Y ω).rpow (1 - α) := by
            rw [abs_of_nonneg hXω_nonneg, abs_of_nonneg hYω_nonneg]
      _ ≤ α * X ω + (1 - α) * Y ω := hω

/-- The weighted geometric mean `(x, y) ↦ x^α y^(1-α)` is concave on the nonnegative quadrant for
weights `α ∈ [0, 1]`. -/
private theorem concaveOn_nonneg_weightedGeometricMean {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ConcaveOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ))
      (fun z : ℝ × ℝ ↦ z.1.rpow α * z.2.rpow (1 - α)) := by
  rcases eq_or_lt_of_le hα0 with rfl | hα0'
  · -- When `α = 0`, the weighted geometric mean is just the second coordinate projection.
    refine ⟨(convex_Ici (0 : ℝ)).prod (convex_Ici (0 : ℝ)), ?_⟩
    intro x hx y hy a b ha hb hab
    simp [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_add]
  rcases eq_or_lt_of_le hα1 with rfl | hα1'
  · -- When `α = 1`, the weighted geometric mean is just the first coordinate projection.
    refine ⟨(convex_Ici (0 : ℝ)).prod (convex_Ici (0 : ℝ)), ?_⟩
    intro x hx y hy a b ha hb hab
    simp [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  refine ⟨(convex_Ici (0 : ℝ)).prod (convex_Ici (0 : ℝ)), ?_⟩
  intro x hx y hy a b ha hb hab
  -- Route correction: the product-concavity API needs an antivary hypothesis, so we prove the
  -- defining inequality directly from the two-point Hölder estimate.
  simpa [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    (sum_weightedGeometricMean_le_weightedGeometricMean_sum hα0' hα1' ha hb
      hx.1 hx.2 hy.1 hy.2)

/-- Example 7.13: if `α ∈ [0,1]` and `X`, `Y` are nonnegative integrable random variables, then
the expectation of `X^α Y^(1-α)` is bounded above by the weighted geometric mean of the
expectations of `X` and `Y`, i.e. Jensen's inequality for the concave map
`(x, y) ↦ x^α y^(1-α)` on the nonnegative quadrant. -/
theorem expectation_weighted_geometricMean_le_weighted_geometricMean_expectations
    {P : Measure Ω} [IsProbabilityMeasure P] {α : ℝ} {X Y : Ω → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hX : Integrable X P) (hY : Integrable Y P)
    (hX_nonneg : 0 ≤ᵐ[P] X) (hY_nonneg : 0 ≤ᵐ[P] Y) :
    P[fun ω ↦ (X ω).rpow α * (Y ω).rpow (1 - α)] ≤
      (P[X]).rpow α * (P[Y]).rpow (1 - α) := by
  let s : Set (ℝ × ℝ) := Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)
  let g : ℝ × ℝ → ℝ := fun z ↦ z.1.rpow α * z.2.rpow (1 - α)
  let f : Ω → ℝ × ℝ := fun ω ↦ (X ω, Y ω)
  have h1α0 : 0 ≤ 1 - α := sub_nonneg.2 hα1
  have hfi : Integrable f P := hX.prodMk hY
  have hgc : ContinuousOn g s := by
    -- Each coordinate `rpow` is continuous for nonnegative exponents, so their product is too.
    have hfst : Continuous fun z : ℝ × ℝ ↦ z.1.rpow α :=
      (Real.continuous_rpow_const hα0).comp continuous_fst
    have hsnd : Continuous fun z : ℝ × ℝ ↦ z.2.rpow (1 - α) :=
      (Real.continuous_rpow_const h1α0).comp continuous_snd
    exact (hfst.mul hsnd).continuousOn
  have hsc : IsClosed s := isClosed_Ici.prod isClosed_Ici
  have hfs : ∀ᵐ ω ∂P, f ω ∈ s := by
    filter_upwards [hX_nonneg, hY_nonneg] with ω hXω hYω
    exact ⟨hXω, hYω⟩
  have hgi : Integrable (g ∘ f) P :=
    integrable_weightedGeometricMean hα0 hα1 hX hY hX_nonneg hY_nonneg
  -- Apply Jensen to the random vector `(X, Y)` on the closed convex nonnegative quadrant.
  simpa [g, f, s, integral_pair hX hY] using
    (ConcaveOn.le_map_integral (μ := P) (s := s) (g := g) (f := f)
      (concaveOn_nonneg_weightedGeometricMean hα0 hα1) hgc hsc hfs hfi hgi)
