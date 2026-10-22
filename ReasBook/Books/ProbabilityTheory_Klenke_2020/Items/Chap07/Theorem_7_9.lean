/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Theorem_7_7

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Theorem 7.9: if an order-connected subset of `ℝ` has a frontier point `m`, then all
its points lie on one side of `m`. -/
private theorem interval_frontier_subset_one_side {I : Set ℝ} (hI : OrdConnected I) {m : ℝ}
    (hm : m ∈ frontier I) :
    I ⊆ Ici m ∨ I ⊆ Iic m := by
  classical
  by_cases h_left : I ⊆ Ici m
  · exact Or.inl h_left
  · right
    intro x hx
    by_contra hxm
    have hmx : m < x := not_le.mp hxm
    rcases not_subset.mp h_left with ⟨y, hyI, hy_not_mem⟩
    have hym : y < m := not_le.mp hy_not_mem
    have hIoo_subset : Ioo x y ⊆ I := by
      intro z hz
      exact hI.out hx hyI ⟨hz.1.le, hz.2.le⟩
    have hm_int : m ∈ interior I := by
      refine mem_interior_iff_mem_nhds.2 ?_
      refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨hym, hmx⟩) ?_
      intro z hz
      exact hI.out hyI hx ⟨hz.1.le, hz.2.le⟩
    exact hm.2 hm_int

/-- Helper for Theorem 7.9: if an interval-valued integrable random variable has expectation on the
frontier of the interval, then it is almost surely constant. -/
private theorem ae_eq_const_of_expectation_mem_frontier_interval {P : Measure Ω}
    [IsProbabilityMeasure P] {I : Set ℝ} {X : Ω → ℝ} (hX : Integrable X P)
    (hXI : ∀ᵐ ω ∂P, X ω ∈ I) (hI : OrdConnected I) (hm : P[X] ∈ frontier I) :
    X =ᵐ[P] fun _ ↦ P[X] := by
  rcases interval_frontier_subset_one_side hI hm with h_right | h_left
  · let m := ∫ ω, X ω ∂P
    let Z : Ω → ℝ := fun ω ↦ X ω - m
    have hZ_nonneg : 0 ≤ᵐ[P] Z := by
      refine hXI.mono ?_
      intro ω hω
      dsimp [Z, m]
      exact sub_nonneg.mpr (h_right hω)
    have hZ_int : Integrable Z P := hX.sub (integrable_const m)
    have hZ_zero : ∫ ω, Z ω ∂P = 0 := by
      -- The centered variable has zero expectation by construction.
      simp [Z, m, integral_sub, hX]
    have hZ_ae_zero : Z =ᵐ[P] 0 := (integral_eq_zero_iff_of_nonneg_ae hZ_nonneg hZ_int).1 hZ_zero
    refine hZ_ae_zero.mono ?_
    intro ω hω
    dsimp [Z, m] at hω ⊢
    linarith
  · let m := ∫ ω, X ω ∂P
    let Z : Ω → ℝ := fun ω ↦ m - X ω
    have hZ_nonneg : 0 ≤ᵐ[P] Z := by
      refine hXI.mono ?_
      intro ω hω
      dsimp [Z, m]
      exact sub_nonneg.mpr (h_left hω)
    have hZ_int : Integrable Z P := (integrable_const m).sub hX
    have hZ_zero : ∫ ω, Z ω ∂P = 0 := by
      -- The centered variable again has zero expectation, now with reversed sign.
      simp [Z, m, integral_sub, hX]
    have hZ_ae_zero : Z =ᵐ[P] 0 := (integral_eq_zero_iff_of_nonneg_ae hZ_nonneg hZ_int).1 hZ_zero
    refine hZ_ae_zero.mono ?_
    intro ω hω
    dsimp [Z, m] at hω ⊢
    linarith

/-- Helper for Theorem 7.9: an integrable real lower bound controls the lower extended expectation
of a possibly nonintegrable real-valued function. -/
private theorem ereal_expectation_ge_of_ae_le {P : Measure Ω} {f g : Ω → ℝ}
    (hg : Integrable g P) (hgf : ∀ᵐ ω ∂P, g ω ≤ f ω) :
    (∫⁻ ω, ENNReal.ofReal (-f ω) ∂P) < ⊤ ∧
      ((((∫⁻ ω, ENNReal.ofReal (f ω) ∂P) : EReal) -
          ((∫⁻ ω, ENNReal.ofReal (-f ω) ∂P) : EReal)) ≥
        ((∫ ω, g ω ∂P : ℝ) : EReal)) := by
  have hneg_fin : (∫⁻ ω, ENNReal.ofReal (-f ω) ∂P) < ⊤ := by
    have hneg_int : Integrable (fun ω ↦ -g ω) P := hg.neg
    -- Proof comment: a real-valued integrable lower bound dominates the negative part of `f`.
    have hbound : ∀ᵐ ω ∂P, ENNReal.ofReal (-f ω) ≤ ENNReal.ofReal (-g ω) := by
      filter_upwards [hgf] with ω hω
      exact ENNReal.ofReal_le_ofReal (neg_le_neg hω)
    exact lt_of_le_of_lt (lintegral_mono_ae hbound) hneg_int.lintegral_lt_top
  have hpos : ∀ᵐ ω ∂P, ENNReal.ofReal (g ω) ≤ ENNReal.ofReal (f ω) := by
    filter_upwards [hgf] with ω hω
    exact ENNReal.ofReal_le_ofReal hω
  have hneg : ∀ᵐ ω ∂P, ENNReal.ofReal (-f ω) ≤ ENNReal.ofReal (-g ω) := by
    filter_upwards [hgf] with ω hω
    exact ENNReal.ofReal_le_ofReal (neg_le_neg hω)
  have hmain :
      (((∫⁻ ω, ENNReal.ofReal (g ω) ∂P) : EReal) -
          ((∫⁻ ω, ENNReal.ofReal (-g ω) ∂P) : EReal)) ≤
        (((∫⁻ ω, ENNReal.ofReal (f ω) ∂P) : EReal) -
          ((∫⁻ ω, ENNReal.ofReal (-f ω) ∂P) : EReal)) := by
    -- Proof comment: compare the positive and negative lower integrals separately.
    exact EReal.sub_le_sub
      (by exact_mod_cast lintegral_mono_ae hpos)
      (by exact_mod_cast lintegral_mono_ae hneg)
  have hident :
      (((∫⁻ ω, ENNReal.ofReal (g ω) ∂P) : EReal) -
          ((∫⁻ ω, ENNReal.ofReal (-g ω) ∂P) : EReal)) =
        (∫ ω, g ω ∂P : ℝ) := by
    have hpos_ne_top : (∫⁻ ω, ENNReal.ofReal (g ω) ∂P) ≠ ⊤ := hg.lintegral_lt_top.ne
    have hneg_int : Integrable (fun ω ↦ -g ω) P := hg.neg
    have hneg_ne_top : (∫⁻ ω, ENNReal.ofReal (-g ω) ∂P) ≠ ⊤ := hneg_int.lintegral_lt_top.ne
    -- Proof comment: for the integrable lower bound `g`, the textbook `EReal` expression is the
    -- ordinary real integral.
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg]
    rw [← EReal.coe_ennreal_toReal hpos_ne_top, ← EReal.coe_ennreal_toReal hneg_ne_top]
    norm_num
  exact ⟨hneg_fin, hident.ge.trans hmain⟩

-- Proof sketch: replace `X` by a measurable representative, then split according to whether its
-- expectation lies in the interior or on the frontier of the interval. In the interior case, a
-- supporting tangent line gives an integrable affine lower bound. In the frontier case, the
-- interval constraint forces almost sure constancy.
/-- Theorem 7.9: Jensen's inequality for an integrable real random variable taking values in a
set on which `φ` is convex. The negative part of `φ ∘ X` has finite expectation, and the
extended expectation of `φ(X)`, written canonically as the difference of the lower integrals of
its positive and negative parts, is at least `φ` evaluated at the expectation of `X`. -/
theorem convexOn_erealExpectation_comp_ge {P : Measure Ω} [IsProbabilityMeasure P] {I : Set ℝ}
    {X : Ω → ℝ} {φ : ℝ → ℝ} (hX : Integrable X P) (hXI : ∀ᵐ ω ∂P, X ω ∈ I)
    (hφ : ConvexOn ℝ I φ) :
    (∫⁻ ω, ENNReal.ofReal (-φ (X ω)) ∂P) < ⊤ ∧
      (((∫⁻ ω, ENNReal.ofReal (φ (X ω)) ∂P) : EReal) -
          ((∫⁻ ω, ENNReal.ofReal (-φ (X ω)) ∂P) : EReal)) ≥
        (φ (P[X]) : EReal) := by
  let m : ℝ := P[X]
  have hm_closure : m ∈ closure I := by
    -- Proof comment: the expectation of an interval-valued integrable random variable lies in the
    -- closure of the interval.
    simpa [m] using
      hφ.1.closure.integral_mem isClosed_closure
        (hXI.mono fun ω hω ↦ subset_closure hω) hX
  by_cases hm_int : m ∈ interior I
  · let t : ℝ := derivWithin φ (Ioi m) m
    let g : ℝ → ℝ := fun x ↦ t * x + (φ m - t * m)
    have hsupportingSlope : ∀ y ∈ I, φ m + t * (y - m) ≤ φ y := by
      refine (convexOn_supportingSlope_iff hφ hm_int).2 ?_
      dsimp [t]
      exact ⟨hφ.leftDeriv_le_rightDeriv_of_mem_interior hm_int, le_rfl⟩
    have hsupport : ∀ y ∈ I, g y ≤ φ y := by
      intro y hy
      have hy' := hsupportingSlope y hy
      dsimp [g] at hy' ⊢
      linarith
    have hg_int : Integrable (fun ω ↦ g (X ω)) P := by
      -- Proof comment: the supporting affine minorant is integrable because `X` is integrable.
      simpa [g] using (hX.const_mul t).add (integrable_const (φ m - t * m))
    have hgf : ∀ᵐ ω ∂P, g (X ω) ≤ φ (X ω) := by
      filter_upwards [hXI] with ω hω
      exact hsupport (X ω) hω
    obtain ⟨hneg_fin, hbound⟩ :=
      ereal_expectation_ge_of_ae_le hg_int hgf
    have hg_expect : ∫ ω, g (X ω) ∂P = φ m := by
      -- Proof comment: the supporting affine minorant was chosen to touch `φ` at the barycenter.
      rw [show (fun ω ↦ g (X ω)) = fun ω ↦ t * X ω + (φ m - t * m) by
            funext ω
            simp [g]]
      rw [integral_add (hX.const_mul t) (integrable_const (φ m - t * m))]
      rw [integral_const_mul, integral_const, probReal_univ, one_smul]
      dsimp [m]
      ring
    refine ⟨hneg_fin, ?_⟩
    calc
      (((∫⁻ ω, ENNReal.ofReal (φ (X ω)) ∂P) : EReal) -
          ((∫⁻ ω, ENNReal.ofReal (-φ (X ω)) ∂P) : EReal)) ≥
          ((∫ ω, g (X ω) ∂P : ℝ) : EReal) := hbound
      _ = (φ m : EReal) := by simp [hg_expect]
      _ = (φ (P[X]) : EReal) := by simp [m]
  · -- Route correction: the earlier measurable-extension route is unnecessary. At a frontier point,
    -- interval rigidity already forces `X` to be almost surely constant.
    have hm_frontier : m ∈ frontier I := by
      rw [frontier]
      exact ⟨hm_closure, hm_int⟩
    have hI : OrdConnected I := hφ.1.ordConnected
    have hX_const : X =ᵐ[P] fun _ ↦ m :=
      ae_eq_const_of_expectation_mem_frontier_interval hX hXI hI hm_frontier
    have hφX_eq : (fun ω ↦ φ (X ω)) =ᵐ[P] fun _ ↦ φ m := by
      refine hX_const.mono ?_
      intro ω hω
      simp [hω]
    have hconst_int : Integrable (fun _ : Ω ↦ φ m) P := integrable_const (φ m)
    have hconst_le : ∀ᵐ ω ∂P, φ m ≤ φ (X ω) := by
      filter_upwards [hφX_eq] with ω hω
      simp [hω]
    obtain ⟨hneg_fin, hbound⟩ :=
      ereal_expectation_ge_of_ae_le hconst_int hconst_le
    refine ⟨hneg_fin, ?_⟩
    simpa [integral_const, probReal_univ, one_smul, m] using hbound
