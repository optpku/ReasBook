/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.Defs

noncomputable section

/-
Domain sampling for this item:
- primary domain: real inner-product-space norm/angle inequalities;
- sampled canonical declarations in this domain:
  `real_inner_self_eq_norm_sq`,
  `inner_sub_left`,
  `inner_sub_right`,
  `real_inner_le_norm`;
- best owner abstraction: the real inner product on an arbitrary real inner product space;
- primitive data here: vectors `u v` together with the norm-control hypotheses;
- derived API here: the `ℝ^n`/`dotProduct` presentation, obtained by specializing to
  `EuclideanSpace ℝ (Fin n)`.

The public surface is therefore the intrinsic real inner product `⟪u, v⟫_ℝ`; the Euclidean
`dotProduct` model is only a specialization bridge and not the owner layer of this file.
-/

section Chapter05Lemma545

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for Chapter05 Lemma 5.4.5: the `PreInnerProductSpace.Core` structure induced by the
ambient real inner-product space. -/
local instance innerProductSpaceCore : PreInnerProductSpace.Core ℝ E :=
  PreInnerProductSpace.toCore

/-- Helper for Chapter05 Lemma 5.4.5: in a real inner-product space,
`⟪x, x⟫_ℝ = ‖x‖ ^ 2`. -/
lemma realInnerSelfEqNormSq (x : E) : ⟪x, x⟫_ℝ = ‖x‖ ^ (2 : ℕ) := by
  simpa using (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ) x).symm

/-- Helper for Chapter05 Lemma 5.4.5: the real inner product is symmetric. -/
lemma realInnerComm (x y : E) : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by
  simpa using (InnerProductSpace.Core.inner_conj_symm (𝕜 := ℝ) x y)

/-- Helper for Chapter05 Lemma 5.4.5: the real inner product is bounded by the product of norms. -/
lemma absRealInnerLeNorm (x y : E) : |⟪x, y⟫_ℝ| ≤ ‖x‖ * ‖y‖ := by
  have hcore :=
    @InnerProductSpace.Core.norm_inner_le_norm ℝ E _ _ _ innerProductSpaceCore x y
  have hx : @norm E (@InnerProductSpace.Core.toNorm ℝ E _ _ _ innerProductSpaceCore) x = ‖x‖ := by
    change Real.sqrt (RCLike.re ⟪x, x⟫_ℝ) = ‖x‖
    rw [← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ) x, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg x)]
  have hy : @norm E (@InnerProductSpace.Core.toNorm ℝ E _ _ _ innerProductSpaceCore) y = ‖y‖ := by
    change Real.sqrt (RCLike.re ⟪y, y⟫_ℝ) = ‖y‖
    rw [← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ) y, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg y)]
  simpa [Real.norm_eq_abs, hx, hy] using hcore

/-- Helper for Chapter05 Lemma 5.4.5: `⟪x, y⟫_ℝ ≤ ‖x‖ * ‖y‖`. -/
lemma realInnerLeNorm (x y : E) : ⟪x, y⟫_ℝ ≤ ‖x‖ * ‖y‖ := by
  exact (le_abs_self _).trans (absRealInnerLeNorm x y)

/-- Helper for Chapter05 Lemma 5.4.5: the normalized real inner product has absolute value at
most `1`. -/
lemma absRealInnerDivNormMulNormLeOne (x y : E) :
    |⟪x, y⟫_ℝ / (‖x‖ * ‖y‖)| ≤ 1 := by
  have hnorm : |⟪x, y⟫_ℝ| ≤ ‖x‖ * ‖y‖ := absRealInnerLeNorm x y
  have hden : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg x) (norm_nonneg y)
  calc
    |⟪x, y⟫_ℝ / (‖x‖ * ‖y‖)| = |⟪x, y⟫_ℝ| / (‖x‖ * ‖y‖) := by
      rw [abs_div, abs_of_nonneg hden]
    _ ≤ 1 := div_le_one_of_le₀ hnorm hden

/-- Helper for Chapter05 Lemma 5.4.5: the squared norm of `x - y` expands by the real inner
product identity. -/
lemma normSubSqReal (x y : E) :
    ‖x - y‖ ^ (2 : ℕ) = ‖x‖ ^ (2 : ℕ) - 2 * ⟪x, y⟫_ℝ + ‖y‖ ^ (2 : ℕ) := by
  calc
    ‖x - y‖ ^ (2 : ℕ) = ⟪x - y, x - y⟫_ℝ := by
      symm
      exact realInnerSelfEqNormSq (x - y)
    _ = ⟪x, x⟫_ℝ - ⟪x, y⟫_ℝ - ⟪y, x⟫_ℝ + ⟪y, y⟫_ℝ := by
      rw [InnerProductSpace.Core.inner_sub_left (𝕜 := ℝ),
        InnerProductSpace.Core.inner_sub_right (𝕜 := ℝ),
        InnerProductSpace.Core.inner_sub_right (𝕜 := ℝ)]
      ring
    _ = ‖x‖ ^ (2 : ℕ) - 2 * ⟪x, y⟫_ℝ + ‖y‖ ^ (2 : ℕ) := by
      rw [realInnerSelfEqNormSq, realInnerSelfEqNormSq, realInnerComm]
      ring

/-- Helper for Chapter05 Lemma 5.4.5: for nonzero `u` and `α < 1`, the closeness hypothesis
`‖u - v‖ ≤ α * ‖u‖` implies `0 < ⟪u, v⟫_ℝ`. -/
theorem inner_pos_of_norm_sub_le
    (u v : E) (hu : u ≠ 0) (α : ℝ) (hα : α < 1) (hclose : ‖u - v‖ ≤ α * ‖u‖) :
    0 < ⟪u, v⟫_ℝ := by
  -- Decompose `‖u‖²` into `⟪u, v⟫ + ⟪u, u - v⟫` and bound the error term by Cauchy-Schwarz.
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hclose_lt : ‖u - v‖ < ‖u‖ := by
    nlinarith
  have hcs : |⟪u, u - v⟫_ℝ| ≤ ‖u‖ * ‖u - v‖ := absRealInnerLeNorm u (u - v)
  have hcs_upper : ⟪u, u - v⟫_ℝ ≤ ‖u‖ * ‖u - v‖ := (abs_le.mp hcs).2
  have hdecomp : v + (u - v) = u := by
    abel
  have hrewrite : ‖u‖ ^ (2 : ℕ) = ⟪u, v⟫_ℝ + ⟪u, u - v⟫_ℝ := by
    calc
      ‖u‖ ^ (2 : ℕ) = ⟪u, u⟫_ℝ := by symm; exact realInnerSelfEqNormSq u
      _ = ⟪u, v + (u - v)⟫_ℝ := by rw [hdecomp]
      _ = ⟪u, v⟫_ℝ + ⟪u, u - v⟫_ℝ := by
        exact InnerProductSpace.Core.inner_add_right (𝕜 := ℝ) u v (u - v)
  nlinarith

end Chapter05Lemma545

section Chapter05Lemma545NormControl

variable {E : Type*} [NormedAddCommGroup E]

/-- Helper for Chapter05 Lemma 5.4.5: for nonzero `u`, the hypothesis
`‖u - v‖ ≤ α * ‖u‖` implies `|1 - ‖v‖ / ‖u‖| ≤ α`. -/
theorem abs_one_sub_norm_div_norm_le_of_norm_sub_le
    (u v : E) (hu : u ≠ 0) (α : ℝ) (hclose : ‖u - v‖ ≤ α * ‖u‖) :
    |1 - ‖v‖ / ‖u‖| ≤ α := by
  -- Normalize the closeness hypothesis by dividing the standard norm-gap estimate by `‖u‖`.
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hgap : |‖u‖ - ‖v‖| ≤ α * ‖u‖ := (abs_norm_sub_norm_le u v).trans hclose
  have hratio : 1 - ‖v‖ / ‖u‖ = (‖u‖ - ‖v‖) / ‖u‖ := by
    field_simp [hu0.ne']
  have hdiv : |‖u‖ - ‖v‖| / ‖u‖ ≤ α := by
    rw [div_le_iff₀ hu0]
    simpa [abs_of_nonneg hu0.le] using hgap
  calc
    |1 - ‖v‖ / ‖u‖| = |(‖u‖ - ‖v‖) / ‖u‖| := by rw [hratio]
    _ = |‖u‖ - ‖v‖| / ‖u‖ := by rw [abs_div, abs_of_pos hu0]
    _ ≤ α := hdiv

end Chapter05Lemma545NormControl

section Chapter05Lemma545

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for Chapter05 Lemma 5.4.5: the `PreInnerProductSpace.Core` structure induced by the
ambient real inner-product space in the reopened inner-product section. -/
local instance innerProductSpaceCore' : PreInnerProductSpace.Core ℝ E :=
  PreInnerProductSpace.toCore

/-- Helper for Chapter05 Lemma 5.4.5: the normalized inner-product defect is controlled by the
relative squared distance when both vectors are nonzero. -/
lemma normalized_inner_defect_le_norm_sub_ratio_sq
    (u v : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    1 - (⟪u, v⟫_ℝ / (‖u‖ * ‖v‖)) ^ (2 : ℕ) ≤ (‖u - v‖ / ‖u‖) ^ (2 : ℕ) := by
  -- Clear denominators once, then the target becomes a polynomial inequality.
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hsq : 0 ≤ (‖v‖ ^ (2 : ℕ) - ⟪u, v⟫_ℝ) ^ (2 : ℕ) := sq_nonneg _
  field_simp [pow_two, hu0.ne', hv0.ne']
  nlinarith [normSubSqReal u v, hsq]

/-- Helper for Chapter05 Lemma 5.4.5: for nonzero `u`, the hypothesis
`‖u - v‖ ≤ α * ‖u‖` implies
`1 - (⟪u, v⟫_ℝ / (‖u‖ * ‖v‖)) ^ (2 : ℕ) ≤ α ^ (2 : ℕ)`. -/
theorem one_sub_sq_normalizedInner_le_of_norm_sub_le
    (u v : E) (hu : u ≠ 0) (α : ℝ) (hclose : ‖u - v‖ ≤ α * ‖u‖) :
    1 - (⟪u, v⟫_ℝ / (‖u‖ * ‖v‖)) ^ (2 : ℕ) ≤ α ^ (2 : ℕ) := by
  -- Split off the degenerate `v = 0` case, because real division by zero is defined.
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
  by_cases hv : v = 0
  · subst hv
    have halpha_ge_one : 1 ≤ α := by
      have hscaled : ‖u‖ ≤ α * ‖u‖ := by simpa using hclose
      nlinarith
    have hα0 : 0 ≤ α := le_trans zero_le_one halpha_ge_one
    have halpha_sq : (1 : ℝ) ^ (2 : ℕ) ≤ α ^ (2 : ℕ) := by
      exact (sq_le_sq₀ zero_le_one hα0).2 halpha_ge_one
    simpa [pow_two, hu0.ne'] using halpha_sq
  · have hα0 : 0 ≤ α := by
      have hscaled_nonneg : 0 ≤ α * ‖u‖ := le_trans (norm_nonneg (u - v)) hclose
      nlinarith
    have hratio : ‖u - v‖ / ‖u‖ ≤ α := by
      rw [div_le_iff₀ hu0]
      simpa using hclose
    have hratio_nonneg : 0 ≤ ‖u - v‖ / ‖u‖ := by positivity
    have hratio_sq : (‖u - v‖ / ‖u‖) ^ (2 : ℕ) ≤ α ^ (2 : ℕ) := by
      exact (sq_le_sq₀ hratio_nonneg hα0).2 hratio
    exact (normalized_inner_defect_le_norm_sub_ratio_sq u v hu hv).trans hratio_sq

/-- Helper for Chapter05 Lemma 5.4.5: `‖u - v‖²` splits into a norm-gap term and an angle term
when both vectors are nonzero. -/
lemma norm_sub_sq_eq_norm_gap_sq_add_angle_term
    (u v : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖u - v‖ ^ (2 : ℕ) =
      (‖u‖ - ‖v‖) ^ (2 : ℕ) + 2 * ‖u‖ * ‖v‖ * (1 - ⟪u, v⟫_ℝ / (‖u‖ * ‖v‖)) := by
  -- This is the exact square decomposition used in the converse direction.
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  calc
    ‖u - v‖ ^ (2 : ℕ) = ‖u‖ ^ (2 : ℕ) - 2 * ⟪u, v⟫_ℝ + ‖v‖ ^ (2 : ℕ) := normSubSqReal u v
    _ = (‖u‖ - ‖v‖) ^ (2 : ℕ) + 2 * ‖u‖ * ‖v‖ * (1 - ⟪u, v⟫_ℝ / (‖u‖ * ‖v‖)) := by
      field_simp [pow_two, hu0.ne', hv0.ne']
      ring

/-- Chapter05 Lemma 5.4.5 (4): if `0 < ⟪u, v⟫_ℝ` and the two inequalities in `(5.4.17)` hold,
then `‖u - v‖ ≤ (3 * α) * ‖u‖`. -/
theorem norm_sub_le_three_mul_of_inner_pos_and_controls
    (u v : E) (α : ℝ) (hpos : 0 < ⟪u, v⟫_ℝ)
    (hnorm : |1 - ‖v‖ / ‖u‖| ≤ α)
    (hangle : 1 - (⟪u, v⟫_ℝ / (‖u‖ * ‖v‖)) ^ (2 : ℕ) ≤ α ^ (2 : ℕ)) :
    ‖u - v‖ ≤ (3 * α) * ‖u‖ := by
  -- The converse follows from the norm-gap/angle decomposition and a case split on `α ≤ 1`.
  have hu : u ≠ 0 := by
    intro hu0
    have : ⟪u, v⟫_ℝ = 0 := by
      simpa [hu0] using (InnerProductSpace.Core.inner_zero_left (𝕜 := ℝ) v)
    linarith
  have hv : v ≠ 0 := by
    intro hv0
    have : ⟪u, v⟫_ℝ = 0 := by
      simpa [hv0] using (InnerProductSpace.Core.inner_zero_right (𝕜 := ℝ) u)
    linarith
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hα0 : 0 ≤ α := by
    have habs_nonneg : 0 ≤ |1 - ‖v‖ / ‖u‖| := abs_nonneg _
    linarith
  have hratio : 1 - ‖v‖ / ‖u‖ = (‖u‖ - ‖v‖) / ‖u‖ := by
    field_simp [hu0.ne']
  have hgap_abs : |‖u‖ - ‖v‖| ≤ α * ‖u‖ := by
    have hdiv : |(‖u‖ - ‖v‖) / ‖u‖| ≤ α := by
      simpa [hratio] using hnorm
    rwa [abs_div, abs_of_pos hu0, div_le_iff₀ hu0] at hdiv
  have hv_le : ‖v‖ ≤ (1 + α) * ‖u‖ := by
    rcases abs_le.mp hnorm with ⟨hlow, _⟩
    have hdiv : ‖v‖ / ‖u‖ ≤ 1 + α := by
      linarith
    rwa [div_le_iff₀ hu0] at hdiv
  let ω : ℝ := ⟪u, v⟫_ℝ / (‖u‖ * ‖v‖)
  have hω_pos : 0 < ω := by
    dsimp [ω]
    exact div_pos hpos (mul_pos hu0 hv0)
  have hω_le_one : ω ≤ 1 := by
    have habs : |ω| ≤ 1 := by
      simpa [ω] using absRealInnerDivNormMulNormLeOne u v
    simpa [abs_of_nonneg hω_pos.le] using habs
  have hone_sub_nonneg : 0 ≤ 1 - ω := sub_nonneg.mpr hω_le_one
  have hone_sub : 1 - ω ≤ α ^ (2 : ℕ) := by
    have hωsq : 1 - ω ^ (2 : ℕ) ≤ α ^ (2 : ℕ) := by
      simpa [ω] using hangle
    have hfactor : 1 - ω ^ (2 : ℕ) = (1 - ω) * (1 + ω) := by
      ring
    have hmul : (1 - ω) * (1 + ω) ≤ α ^ (2 : ℕ) := by
      simpa [hfactor] using hωsq
    have hle : 1 - ω ≤ (1 - ω) * (1 + ω) := by
      nlinarith
    exact hle.trans hmul
  by_cases hα1 : α ≤ 1
  · have hgap_sq : (‖u‖ - ‖v‖) ^ (2 : ℕ) ≤ (α * ‖u‖) ^ (2 : ℕ) := by
      rw [sq_le_sq, abs_of_nonneg (mul_nonneg hα0 hu0.le)]
      exact hgap_abs
    have hv_le_two : ‖v‖ ≤ 2 * ‖u‖ := by
      nlinarith
    have hangle_term :
        2 * ‖u‖ * ‖v‖ * (1 - ω) ≤ 4 * α ^ (2 : ℕ) * ‖u‖ ^ (2 : ℕ) := by
      have hfac₁ : 0 ≤ 2 * ‖u‖ * (1 - ω) := by positivity
      have hstep₁ :
          (2 * ‖u‖ * (1 - ω)) * ‖v‖ ≤ (2 * ‖u‖ * (1 - ω)) * (2 * ‖u‖) := by
        exact mul_le_mul_of_nonneg_left hv_le_two hfac₁
      have hfac₂ : 0 ≤ 2 * ‖u‖ * (2 * ‖u‖) := by positivity
      have hstep₂ :
          (2 * ‖u‖ * (2 * ‖u‖)) * (1 - ω) ≤ (2 * ‖u‖ * (2 * ‖u‖)) * (α ^ (2 : ℕ)) := by
        exact mul_le_mul_of_nonneg_left hone_sub hfac₂
      nlinarith [hstep₁, hstep₂]
    have hsq : ‖u - v‖ ^ (2 : ℕ) ≤ ((3 * α) * ‖u‖) ^ (2 : ℕ) := by
      calc
        ‖u - v‖ ^ (2 : ℕ)
            = (‖u‖ - ‖v‖) ^ (2 : ℕ) + 2 * ‖u‖ * ‖v‖ * (1 - ω) := by
              simpa [ω] using norm_sub_sq_eq_norm_gap_sq_add_angle_term u v hu hv
        _ ≤ (α * ‖u‖) ^ (2 : ℕ) + 4 * α ^ (2 : ℕ) * ‖u‖ ^ (2 : ℕ) := by
              exact add_le_add hgap_sq hangle_term
        _ ≤ ((3 * α) * ‖u‖) ^ (2 : ℕ) := by
              nlinarith
    have hright_nonneg : 0 ≤ (3 * α) * ‖u‖ := by positivity
    exact le_of_sq_le_sq hsq hright_nonneg
  · have hα_ge_one : 1 ≤ α := le_of_not_ge hα1
    have htriangle : ‖u - v‖ ≤ ‖u‖ + ‖v‖ := by
      simpa [sub_eq_add_neg] using norm_add_le u (-v)
    nlinarith

end Chapter05Lemma545
