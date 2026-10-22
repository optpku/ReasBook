/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open ERealFunction
open scoped Pointwise

universe u

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- The extended-real Minkowski gauge of a subset of a real vector space. -/
noncomputable def extendedMinkowskiGauge (C : Set H) : H → EReal :=
  fun x ↦ sInf (Real.toEReal '' {ξ : ℝ | 0 < ξ ∧ x ∈ ξ • C})

local notation "m[" C "]" =>
  extendedMinkowskiGauge C

/-- Helper for Example 8.36: every Minkowski gauge value is nonnegative because the defining
infimum ranges over positive real scalars only. -/
private theorem minkowskiGauge_nonneg (C : Set H) (x : H) :
    0 ≤ m[C] x := by
  -- Rewrite the infimum over an image as an iterated infimum over admissible positive scalars.
  rw [extendedMinkowskiGauge, sInf_image]
  refine le_iInf ?_
  intro ξ
  refine le_iInf ?_
  intro hξ
  exact EReal.coe_nonneg.2 hξ.1.le

/-- Helper for Example 8.36: nonnegativity rules out the value `-∞` for the Minkowski gauge. -/
private theorem minkowskiGauge_ne_bot (C : Set H) (x : H) :
    m[C] x ≠ ⊥ := by
  -- A nonnegative extended real cannot equal `⊥`.
  intro hbot
  simpa [hbot] using minkowskiGauge_nonneg C x

/-- Helper for Example 8.36: on the effective domain, the gauge coincides with its real part. -/
private theorem minkowskiGauge_coe_toReal (C : Set H) {x : H} (hx : x ∈ dom (m[C])) :
    ((m[C] x).toReal : EReal) = m[C] x := by
  -- Domain membership gives finiteness above, while nonnegativity excludes `-∞`.
  have htop : m[C] x ≠ ⊤ := ne_of_lt hx
  exact EReal.coe_toReal htop (minkowskiGauge_ne_bot C x)

/-- Helper for Example 8.36: any concrete scaled-set witness gives an upper bound on the gauge. -/
private theorem minkowskiGauge_le_of_mem_smul (C : Set H) {x : H} {ξ : ℝ}
    (hξ : 0 < ξ) (hx : x ∈ ξ • C) :
    m[C] x ≤ (ξ : EReal) := by
  -- The witness scalar belongs to the set whose infimum defines `m[C] x`.
  dsimp [extendedMinkowskiGauge]
  exact sInf_le ⟨ξ, ⟨hξ, hx⟩, rfl⟩

/-- Helper for Example 8.36: a strict real upper bound on the gauge produces an admissible
positive scalar strictly below that bound. -/
private theorem exists_mem_smul_of_minkowskiGauge_lt (C : Set H) {x : H} {r : ℝ}
    (hr : m[C] x < (r : EReal)) :
    ∃ ξ : ℝ, 0 < ξ ∧ ξ < r ∧ x ∈ ξ • C := by
  -- If every admissible witness were at least `r`, the defining infimum would also be at least `r`.
  by_contra h
  have hrle : (r : EReal) ≤ m[C] x := by
    rw [extendedMinkowskiGauge, sInf_image]
    refine le_iInf ?_
    intro ξ
    refine le_iInf ?_
    intro hξ
    have hnot_lt : ¬ ξ < r := by
      intro hlt
      exact h ⟨ξ, hξ.1, hlt, hξ.2⟩
    have hle : r ≤ ξ := le_of_not_gt hnot_lt
    simpa using hle
  exact (not_le_of_gt hr) hrle

/-- Helper for Example 8.36: scaling a witness by a positive scalar scales the admissible set
parameter in the same way. -/
private theorem scale_mem_of_mem_smul {C : Set H} {x : H} {a ξ : ℝ} (hx : x ∈ ξ • C) :
    a • x ∈ (a * ξ) • C := by
  -- Expand the pointwise-set membership and move the outside scalar through the representation.
  rcases hx with ⟨y, hy, rfl⟩
  refine ⟨y, hy, ?_⟩
  rw [smul_smul, mul_comm]

/-- Helper for Example 8.36: a positive witness for `a • x` in `ξ • C` descends to a witness for
`x` in `(ξ / a) • C`. -/
private theorem mem_div_smul_of_smul_mem {C : Set H} {x : H} {a ξ : ℝ} (ha : 0 < a)
    (hξ : 0 < ξ) (hx : a • x ∈ ξ • C) :
    x ∈ (ξ / a) • C := by
  -- Normalize the source membership and rewrite the target normalization to the same point of `C`.
  have hnorm : ξ⁻¹ • (a • x) ∈ C := by
    exact (Set.mem_smul_set_iff_inv_smul_mem₀ hξ.ne' C (a • x)).1 hx
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (div_ne_zero hξ.ne' ha.ne') C x]
  simpa [div_eq_mul_inv, smul_smul, inv_inv, mul_comm, mul_left_comm, mul_assoc] using hnorm

/-- Helper for Example 8.36: positive scalar dilation of the ambient point is equivalent to
membership in the correspondingly inverse-scaled set. -/
private theorem smul_mem_iff_mem_smul_inv_set {C : Set H} {x : H} {a ξ : ℝ} (ha : 0 < a)
    (hξ : 0 < ξ) :
    a • x ∈ ξ • C ↔ x ∈ ξ • ((a⁻¹ : ℝ) • C) := by
  -- Normalize both memberships by the same positive scalar `ξ`.
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hξ.ne' C (a • x)]
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hξ.ne' ((a⁻¹ : ℝ) • C) x]
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero ha.ne') C (ξ⁻¹ • x)]
  rw [smul_smul, smul_smul, inv_inv, mul_comm ξ⁻¹ a]

/-- Helper for Example 8.36: convexity of `C` combines two scaled-set witnesses into a witness for
the convex combination with the correspondingly averaged scale. -/
private theorem convex_combo_mem_smul (C : Set H) (hC : Convex ℝ C) {x y : H} {ξ η α : ℝ}
    (hx : x ∈ ξ • C) (hy : y ∈ η • C) (hξ : 0 < ξ) (hη : 0 < η) (hα : 0 < α)
    (hα_lt_one : α < 1) :
    α • x + (1 - α) • y ∈ (α * ξ + (1 - α) * η) • C := by
  -- Rewrite both witnesses through points of `C`, then apply convexity with normalized weights.
  rcases hx with ⟨u, hu, rfl⟩
  rcases hy with ⟨v, hv, rfl⟩
  refine ⟨((α * ξ) / (α * ξ + (1 - α) * η)) • u +
      (((1 - α) * η) / (α * ξ + (1 - α) * η)) • v, ?_, ?_⟩
  · have hsum_pos : 0 < α * ξ + (1 - α) * η := by
      nlinarith
    have hu_nonneg : 0 ≤ (α * ξ) / (α * ξ + (1 - α) * η) := by
      exact div_nonneg (by nlinarith) hsum_pos.le
    have hv_nonneg : 0 ≤ ((1 - α) * η) / (α * ξ + (1 - α) * η) := by
      exact div_nonneg (by nlinarith) hsum_pos.le
    have hsum :
        (α * ξ) / (α * ξ + (1 - α) * η) +
            ((1 - α) * η) / (α * ξ + (1 - α) * η) = 1 := by
      field_simp [hsum_pos.ne']
    exact hC hu hv hu_nonneg hv_nonneg hsum
  · have hsum_pos : 0 < α * ξ + (1 - α) * η := by
      nlinarith
    calc
      (α * ξ + (1 - α) * η) •
          (((α * ξ) / (α * ξ + (1 - α) * η)) • u +
            (((1 - α) * η) / (α * ξ + (1 - α) * η)) • v) =
          ((α * ξ + (1 - α) * η) * ((α * ξ) / (α * ξ + (1 - α) * η))) • u +
            ((α * ξ + (1 - α) * η) * (((1 - α) * η) / (α * ξ + (1 - α) * η))) • v := by
            rw [smul_add, smul_smul, smul_smul]
      _ = (α * ξ) • u + ((1 - α) * η) • v := by
            congr 1 <;> field_simp [hsum_pos.ne']
      _ = α • (ξ • u) + (1 - α) • (η • v) := by
            rw [smul_smul, smul_smul]

/-- Helper for Example 8.36: for a convex set containing `0`, increasing the positive scalar only
enlarges the scaled set. -/
private theorem smul_set_mono_of_convex_zero_mem (C : Set H) (hC : Convex ℝ C)
    (h0C : (0 : H) ∈ C) {μ lam : ℝ} (hμ : 0 < μ) (hμlam : μ ≤ lam) :
    μ • C ⊆ lam • C := by
  -- Express a point of `μ • C` as a convex combination inside `λ • C`.
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  by_cases hlam : lam = 0
  · have : False := by
      linarith
    exact False.elim this
  · have hlampos : 0 < lam := by
      linarith
    refine ⟨(μ / lam) • y, ?_, ?_⟩
    · have hμlam_nonneg : 0 ≤ μ / lam := by
        positivity
      have hμlam_le_one : μ / lam ≤ 1 := by
        have hdiv : μ ≤ 1 * lam := by
          simpa using hμlam
        have hquot : μ / lam ≤ 1 := (div_le_iff₀ hlampos).2 hdiv
        simpa using hquot
      have hsum : μ / lam + (1 - μ / lam) = 1 := by
        ring
      simpa [smul_add, add_comm, add_left_comm, add_assoc, one_smul, sub_eq_add_neg, smul_smul] using
        hC hy h0C hμlam_nonneg (sub_nonneg.mpr hμlam_le_one) hsum
    · calc
        lam • ((μ / lam) • y) = (lam * (μ / lam)) • y := by
          rw [smul_smul]
        _ = μ • y := by
          congr 1
          field_simp [hlam]

/-- Helper for Example 8.36: a strict upper bound on the gauge forces membership in the
corresponding scaled set when `C` is convex and contains `0`. -/
private theorem mem_smul_of_minkowskiGauge_lt_aux (C : Set H) (hC : Convex ℝ C)
    (h0C : (0 : H) ∈ C) {x : H} {a : ℝ} (ha : m[C] x < (a : EReal)) :
    x ∈ a • C := by
  -- If `x` were outside `a • C`, every admissible witness scale would have to exceed `a`.
  have haposE : (0 : EReal) < (a : EReal) := by
    exact lt_of_le_of_lt (minkowskiGauge_nonneg C x) ha
  have hapos : 0 < a := EReal.coe_lt_coe_iff.mp haposE
  by_contra hx
  have hbound : (a : EReal) ≤ m[C] x := by
    rw [extendedMinkowskiGauge, sInf_image]
    refine le_iInf ?_
    intro ξ
    refine le_iInf ?_
    intro hξ
    rcases hξ with ⟨hξpos, hxξ⟩
    have hlt : a < ξ := by
      by_contra hnot
      have hξa : ξ ≤ a := le_of_not_gt hnot
      exact hx ((smul_set_mono_of_convex_zero_mem C hC h0C hξpos hξa) hxξ)
    simpa using hlt.le
  exact (not_le_of_gt ha) hbound

-- Proof sketch: view `m[C]` as the marginal of the set-scaling indicator from Example 8.32, whose
-- epigraph is convex when `C` is convex; then apply the marginal-preserves-convexity result from
-- Proposition 8.35.
/-- Example 8.36 (1): if `C` is convex, then the Minkowski gauge `m[C]` has convex epigraph, hence
is a convex extended-real-valued function. -/
theorem convex_epigraph_minkowskiGauge (C : Set H) (hC : Convex ℝ C) :
    Convex ℝ (epigraph (m[C])) := by
  -- Route correction: the finite-valued marginal route does not fit this `EReal`-valued gauge, so
  -- we prove convexity directly on epigraph points by a real-budget argument.
  rw [convex_iff_forall_pos]
  intro p hp q hq a b ha hb hab
  rcases p with ⟨x, t⟩
  rcases q with ⟨y, s⟩
  rw [mem_epigraph_iff] at hp hq ⊢
  have hb_eq : b = 1 - a := by
    linarith
  have ha_lt_one : a < 1 := by
    linarith
  -- To prove the epigraph inequality, it is enough to beat every real budget strictly above the
  -- target height `a * t + b * s`.
  refine le_of_forall_gt_imp_ge_of_dense ?_
  intro (r : EReal) hr
  obtain ⟨ρ, hρ_left, hρ_right⟩ := EReal.exists_between_coe_real hr
  have hρ_left_real : a * t + b * s < ρ := by
    exact EReal.coe_lt_coe_iff.mp (by
      simpa [Prod.smul_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm,
        add_assoc] using hρ_left)
  let δ : ℝ := (ρ - (a * t + b * s)) / 2
  have hδpos : 0 < δ := by
    dsimp [δ]
    linarith [hρ_left_real]
  have hxt :
      m[C] x < ((t + δ : ℝ) : EReal) := by
    exact lt_of_le_of_lt hp (EReal.coe_lt_coe_iff.mpr (by linarith [hδpos]))
  have hys :
      m[C] y < ((s + δ : ℝ) : EReal) := by
    exact lt_of_le_of_lt hq (EReal.coe_lt_coe_iff.mpr (by linarith [hδpos]))
  rcases exists_mem_smul_of_minkowskiGauge_lt C hxt with ⟨ξ, hξpos, hξlt, hxξ⟩
  rcases exists_mem_smul_of_minkowskiGauge_lt C hys with ⟨η, hηpos, hηlt, hyη⟩
  -- Combine endpoint witnesses inside `C`, then push the combined scale back to the gauge.
  have hmem :
      a • x + b • y ∈ (a * ξ + b * η) • C := by
    simpa [hb_eq] using
      (convex_combo_mem_smul C hC hxξ hyη hξpos hηpos ha ha_lt_one)
  have hle :
      m[C] (a • x + b • y) ≤ ((a * ξ + b * η : ℝ) : EReal) :=
    minkowskiGauge_le_of_mem_smul C (by nlinarith) hmem
  have hltρ : a * ξ + b * η < ρ := by
    have hxlt' : a * ξ < a * (t + δ) :=
      mul_lt_mul_of_pos_left hξlt ha
    have hylt' : b * η < b * (s + δ) :=
      mul_lt_mul_of_pos_left hηlt hb
    have hsum_lt : a * ξ + b * η < a * (t + δ) + b * (s + δ) := by
      linarith
    have hbudget_lt : a * (t + δ) + b * (s + δ) < ρ := by
      dsimp [δ]
      nlinarith [hρ_left_real, hab]
    exact lt_trans hsum_lt hbudget_lt
  exact le_of_lt (lt_of_le_of_lt hle (lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hltρ) hρ_right.le))

-- Proof sketch: because `0 ∈ C`, every positive scalar multiple of `C` contains `0`, so the
-- defining infimum for `m[C] 0` is taken over all positive reals and therefore equals `0`.
/-- Example 8.36 (2): if `0 ∈ C`, then the Minkowski gauge of `C` vanishes at the origin. -/
theorem minkowskiGauge_zero (C : Set H) (h0C : (0 : H) ∈ C) :
    m[C] 0 = 0 := by
  refine le_antisymm ?_ (minkowskiGauge_nonneg C 0)
  -- Every real budget above `0` already contains an admissible positive witness for the origin.
  refine le_of_forall_gt_imp_ge_of_dense ?_
  intro (r : EReal) hr
  obtain ⟨ξ, hξpos, hξlt⟩ := EReal.exists_between_coe_real (x := (0 : EReal)) hr
  have hξpos_real : 0 < ξ := EReal.coe_pos.mp hξpos
  have hmem : (0 : H) ∈ ξ • C := by
    refine ⟨0, h0C, ?_⟩
    simp
  have hle : m[C] 0 ≤ (ξ : EReal) := minkowskiGauge_le_of_mem_smul C hξpos_real hmem
  exact le_of_lt (lt_of_le_of_lt hle hξlt)

-- Proof sketch: rewrite membership `λ • x ∈ ξ • C` as `x ∈ (ξ / λ) • C` for `λ > 0`; the
-- admissible positive scalars for `λ • x` are exactly the scalar multiples by `λ` of the
-- admissible positive scalars for `x`, so taking infima scales the gauge by `λ`.
/-- Example 8.36 (3): the Minkowski gauge is positively homogeneous. -/
theorem minkowskiGauge_smul (C : Set H) {x : H} {a : ℝ} (ha : 0 < a) :
    m[C] (a • x) = (a : EReal) * m[C] x := by
  refine le_antisymm ?_ ?_
  · -- Any real budget above `a * m[C] x` yields a scaled witness for `a • x`.
    refine le_of_forall_gt_imp_ge_of_dense ?_
    intro (r : EReal) hr
    by_cases hr_top : r = ⊤
    · simp [hr_top]
    obtain ⟨ρ, hρ_left, hρ_right⟩ := EReal.exists_between_coe_real hr
    have hprod_nonneg : (0 : EReal) ≤ (a : EReal) * m[C] x := by
      exact mul_nonneg (EReal.coe_nonneg.2 ha.le) (minkowskiGauge_nonneg C x)
    have hxdom : x ∈ dom (m[C]) := by
      by_contra hxdom
      have htop : m[C] x = ⊤ := le_antisymm le_top (le_of_not_gt hxdom)
      have htop_prod : ((a : EReal) * m[C] x) = ⊤ := by
        simpa [htop] using (EReal.coe_mul_top_of_pos ha : (a : EReal) * ⊤ = ⊤)
      have htop_r : r = ⊤ := by
        refine le_antisymm le_top ?_
        calc
          ⊤ = (a : EReal) * m[C] x := htop_prod.symm
          _ ≤ r := le_of_lt (lt_of_lt_of_le hρ_left hρ_right.le)
      exact hr_top htop_r
    have hmx : (((m[C] x).toReal : ℝ) : EReal) = m[C] x :=
      minkowskiGauge_coe_toReal C hxdom
    have hbudget : m[C] x < ((ρ / a : ℝ) : EReal) := by
      rw [← hmx]
      apply EReal.coe_lt_coe_iff.2
      have hmul_lt : a * (m[C] x).toReal < ρ := by
        have hρ_left' : ((a * (m[C] x).toReal : ℝ) : EReal) < (ρ : EReal) := by
          calc
            ((a * (m[C] x).toReal : ℝ) : EReal) =
                (a : EReal) * (((m[C] x).toReal : ℝ) : EReal) := by
                  rw [EReal.coe_mul]
            _ = (a : EReal) * m[C] x := by
                  rw [hmx]
            _ < (ρ : EReal) := hρ_left
        exact EReal.coe_lt_coe_iff.1 hρ_left'
      exact (lt_div_iff₀ ha).2 (by simpa [mul_comm] using hmul_lt)
    rcases exists_mem_smul_of_minkowskiGauge_lt C hbudget with ⟨ξ, hξpos, hξlt, hxξ⟩
    have hmem : a • x ∈ (a * ξ) • C := scale_mem_of_mem_smul hxξ
    have hle : m[C] (a • x) ≤ ((a * ξ : ℝ) : EReal) :=
      minkowskiGauge_le_of_mem_smul C (by positivity) hmem
    have hltρ : ((a * ξ : ℝ) : EReal) < (ρ : EReal) := by
      have hltρ_real : a * ξ < ρ := by
        have hmul_lt : ξ * a < ρ := (lt_div_iff₀ ha).1 hξlt
        simpa [mul_comm] using hmul_lt
      exact EReal.coe_lt_coe_iff.2 hltρ_real
    exact le_of_lt (lt_of_le_of_lt hle (lt_of_lt_of_le hltρ hρ_right.le))
  · -- Conversely, a budget above `m[C] (a • x)` descends to a budget above `a * m[C] x`.
    refine le_of_forall_gt_imp_ge_of_dense ?_
    intro (r : EReal) hr
    by_cases hr_top : r = ⊤
    · simp [hr_top]
    obtain ⟨ρ, hρ_left, hρ_right⟩ := EReal.exists_between_coe_real hr
    rcases exists_mem_smul_of_minkowskiGauge_lt C hρ_left with ⟨ξ, hξpos, hξlt, hxξ⟩
    have hxmem : x ∈ (ξ / a) • C := mem_div_smul_of_smul_mem ha hξpos hxξ
    have hle : m[C] x ≤ ((ξ / a : ℝ) : EReal) :=
      minkowskiGauge_le_of_mem_smul C (div_pos hξpos ha) hxmem
    have hmul :
        (a : EReal) * m[C] x ≤ (a : EReal) * ((ξ / a : ℝ) : EReal) := by
      exact mul_le_mul_of_nonneg_left hle (EReal.coe_nonneg.2 ha.le)
    have hcancel : (a : EReal) * ((ξ / a : ℝ) : EReal) = (ξ : EReal) := by
      have hcancel_real : a * (ξ / a) = ξ := by
        field_simp [ha.ne']
      calc
        (a : EReal) * ((ξ / a : ℝ) : EReal) = (((a * (ξ / a)) : ℝ) : EReal) := by
          rw [EReal.coe_mul]
        _ = (ξ : EReal) := congrArg (fun z : ℝ ↦ (z : EReal)) hcancel_real
    have hlt : (a : EReal) * m[C] x < (ρ : EReal) := by
      exact lt_of_le_of_lt (hcancel ▸ hmul) (EReal.coe_lt_coe_iff.2 hξlt)
    exact le_of_lt (lt_of_lt_of_le hlt hρ_right.le)

-- Proof sketch: compare the defining sets
-- `{ξ > 0 | λ • x ∈ ξ • C}` and `{ξ > 0 | x ∈ ξ • ((1 / λ) • C)}`; for `λ > 0` they coincide, so
-- their infima agree.
/-- Example 8.36 (4): scaling the argument by `λ > 0` is equivalent to replacing `C` by
`(1 / λ) • C` in the Minkowski gauge. -/
theorem minkowskiGauge_smul_eq_inv_smul_set (C : Set H) {x : H} {a : ℝ} (ha : 0 < a) :
    m[C] (a • x) = m[(a⁻¹ : ℝ) • C] x := by
  -- Unfold both gauges and identify their admissible scalar sets pointwise.
  dsimp [extendedMinkowskiGauge]
  congr 1
  ext ξ
  constructor
  · rintro ⟨r, ⟨hrpos, hrmem⟩, rfl⟩
    refine ⟨r, ?_, rfl⟩
    exact ⟨hrpos, (smul_mem_iff_mem_smul_inv_set ha hrpos).1 hrmem⟩
  · rintro ⟨r, ⟨hrpos, hrmem⟩, rfl⟩
    refine ⟨r, ?_, rfl⟩
    exact ⟨hrpos, (smul_mem_iff_mem_smul_inv_set ha hrpos).2 hrmem⟩

-- Proof sketch: if `x ∉ λ • C` with `λ > m[C] x`, then convexity of `C` and `0 ∈ C` imply
-- `μ • C ⊆ λ • C` for every `0 < μ ≤ λ`, so no such `μ` can contain `x`; this forces the infimum
-- defining `m[C] x` to be at least `λ`, contradicting `m[C] x < λ`.
/-- Example 8.36 (5): if `C` is convex, contains `0`, and `λ` is strictly larger than the finite
value `m[C] x`, then `x` already belongs to `λ • C`. -/
theorem mem_smul_of_minkowskiGauge_lt (C : Set H) (hC : Convex ℝ C) (h0C : (0 : H) ∈ C)
    {x : H} (hx : x ∈ dom (m[C])) {a : ℝ} (ha : m[C] x < (a : EReal)) :
    x ∈ a • C := by
  -- The domain hypothesis records finiteness, while the contradiction argument uses only the
  -- strict upper bound together with convexity and the presence of `0`.
  have hx_top : m[C] x < ⊤ := hx
  have ha_top : m[C] x < ⊤ := lt_of_lt_of_le ha le_top
  exact mem_smul_of_minkowskiGauge_lt_aux C hC h0C (by exact ha)
