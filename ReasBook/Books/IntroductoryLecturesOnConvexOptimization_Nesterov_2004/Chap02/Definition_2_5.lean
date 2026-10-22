/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open scoped BigOperators

/-
Definition 2.5 lies in the duality domain for dual norms of separated seminorms on real
inner-product spaces, with the source-facing specialization to Euclidean spaces `ℝⁿ`.

Sampled owner-style declarations:
* mathlib `Seminorm.closedBall_zero_eq`
* mathlib `normSeminorm`
* mathlib `closedBall_normSeminorm`
* project `unit_closed_ball_support_function_eq_norm` in `Lemma_2_3`
* project `Seminorm.inner_le_dualNorm_mul` in `Definition_2_5`
* project `supportFunction` in `Chap03/Definition_3_9`

Source/core/bridge triage:
* source-facing: the textbook dual norm of a norm on `ℝⁿ`
* core/canonical: the same owner `p.dualNorm` on a finite-dimensional real inner-product
  space
* bridge/view: `Seminorm.dualNorm_apply`

Primitive data:
* a seminorm `p : Seminorm ℝ E`
* a finite-dimensional real inner-product-space structure on `E`
* the separation hypothesis `[Seminorm.IsNorm p]`

Derived API:
* the support-function formula `Seminorm.dualNorm_apply`
* duality consequences such as `Seminorm.inner_le_dualNorm_mul`
* the Euclidean specialization `Seminorm.dualNorm_normSeminorm_eq_norm` in `Lemma_2_3`
* the operator-norm owner `Seminorm.primalDualOperatorNorm` in `Definition_2_32`

The later Chapter 3 `EReal`-valued `supportFunction` is the more general support-function owner.
Definition 2.5 keeps the source-facing `ℝ`-valued dual norm, with `ℝⁿ` as the textbook ambient
model and finite-dimensional real inner-product spaces as the canonical owner layer.
-/

namespace Seminorm

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- A real seminorm is a norm when only the zero vector has seminorm zero. -/
class IsNorm (p : Seminorm ℝ E) : Prop where
  /-- The only vector with seminorm zero is the zero vector. -/
  eq_zero_of_map_eq_zero {x : E} : p x = 0 → x = 0

/-- A separated seminorm is strictly positive on every nonzero vector. -/
theorem map_pos_of_ne_zero (p : Seminorm ℝ E) [p.IsNorm] {x : E} (hx : x ≠ 0) :
    0 < p x := by
  have hpx_ne : p x ≠ 0 := fun hpx ↦ hx (IsNorm.eq_zero_of_map_eq_zero hpx)
  exact lt_of_le_of_ne (apply_nonneg p x) (Ne.symm hpx_ne)

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The ambient norm on a real normed vector space is a norm in the bundled seminorm sense. -/
instance : IsNorm (normSeminorm ℝ E) where
  eq_zero_of_map_eq_zero {x} hx := by
    exact norm_eq_zero.mp (by simpa using hx : ‖x‖ = 0)

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem le_coordinate_constant_mul_norm (p : Seminorm ℝ E) [FiniteDimensional ℝ E]
    (x : E) :
    p x ≤
      (∑ i, ‖((Module.finBasis ℝ E).coord i).toContinuousLinearMap‖ *
        p ((Module.finBasis ℝ E) i)) * ‖x‖ := by
  let b := Module.finBasis ℝ E
  change p x ≤ (∑ i, ‖(b.coord i).toContinuousLinearMap‖ * p (b i)) * ‖x‖
  have hx : x = ∑ i, (b.repr x i) • b i := by
    exact (b.sum_repr x).symm
  have hsum :
      p (∑ i, (b.repr x i) • b i) ≤
        ∑ i, p ((b.repr x i) • b i) := by
    exact
      Finset.le_sum_of_subadditive p (by simp) (map_add_le_add p) Finset.univ
        (fun i ↦ (b.repr x i) • b i)
  calc
    p x = p (∑ i, (b.repr x i) • b i) := congrArg p hx
    _ ≤ ∑ i, p ((b.repr x i) • b i) := by
      simpa using hsum
    _ = ∑ i, |b.repr x i| * p (b i) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      simpa [Real.norm_eq_abs] using
        (map_smul_eq_mul p (b.repr x i) (b i))
    _ ≤ ∑ i, (‖(b.coord i).toContinuousLinearMap‖ * p (b i)) * ‖x‖ := by
      exact Finset.sum_le_sum fun i _ ↦ by
        have hcoeff :
            |b.repr x i| ≤
              ‖(b.coord i).toContinuousLinearMap‖ * ‖x‖ := by
          simpa [Real.norm_eq_abs] using
            (b.coord i).toContinuousLinearMap.le_opNorm x
        have hpi_nonneg : 0 ≤ p (b i) := apply_nonneg p (b i)
        calc
          |b.repr x i| * p (b i) ≤
              (‖(b.coord i).toContinuousLinearMap‖ * ‖x‖) * p (b i) := by
            exact mul_le_mul_of_nonneg_right hcoeff hpi_nonneg
          _ = (‖(b.coord i).toContinuousLinearMap‖ * p (b i)) * ‖x‖ := by
            ring
    _ = (∑ i, ‖(b.coord i).toContinuousLinearMap‖ * p (b i)) * ‖x‖ := by
      rw [← Finset.sum_mul]

/-- On a finite-dimensional real normed space, a separated seminorm controls the ambient
norm up to a positive constant. -/
theorem exists_norm_le_mul (p : Seminorm ℝ E) [FiniteDimensional ℝ E] [p.IsNorm] :
    ∃ C > 0, ∀ x : E, ‖x‖ ≤ C * p x := by
  by_cases h0 : Module.finrank ℝ E = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x
    letI : Subsingleton E := (Module.finrank_zero_iff (R := ℝ) (M := E)).mp h0
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  · let b := Module.finBasis ℝ E
    let C : ℝ := (∑ i, ‖(b.coord i).toContinuousLinearMap‖ * p (b i)) + 1
    have hC_pos : 0 < C := by
      dsimp [C]
      positivity
    have hp_ball : p.ball 0 1 ∈ nhds (0 : E) := by
      refine Filter.mem_of_superset
        (Metric.ball_mem_nhds (0 : E) (by positivity : 0 < C⁻¹)) ?_
      intro y hy
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hy
      rw [Seminorm.mem_ball_zero]
      calc
        p y ≤ (∑ i, ‖(b.coord i).toContinuousLinearMap‖ * p (b i)) * ‖y‖ := by
          simpa [b] using le_coordinate_constant_mul_norm p y
        _ ≤ C * ‖y‖ := by
          dsimp [C]
          have hsum_le :
              ∑ i, ‖(b.coord i).toContinuousLinearMap‖ * p (b i) ≤ C := by
            linarith
          exact mul_le_mul_of_nonneg_right hsum_le (norm_nonneg _)
        _ < C * C⁻¹ := mul_lt_mul_of_pos_left hy hC_pos
        _ = 1 := by
          rw [mul_inv_cancel₀ hC_pos.ne']
    have hp_cont : Continuous p := Seminorm.continuous hp_ball
    let i0 : Fin (Module.finrank ℝ E) := ⟨0, Nat.pos_of_ne_zero h0⟩
    let u0 : E := ‖b i0‖⁻¹ • b i0
    have hu0 : u0 ∈ Metric.sphere (0 : E) 1 := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      have hbi0_ne : b i0 ≠ 0 := b.ne_zero i0
      have hbi0_norm_pos : 0 < ‖b i0‖ := norm_pos_iff.mpr hbi0_ne
      dsimp [u0]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hbi0_norm_pos.le),
        inv_mul_cancel₀ hbi0_norm_pos.ne']
    have hsphere : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere (0 : E) 1
    obtain ⟨u, hu, hu_min⟩ :=
      hsphere.exists_isMinOn ⟨u0, hu0⟩ hp_cont.continuousOn
    have hu_norm : ‖u‖ = 1 := by
      rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at hu
    have hu_ne : u ≠ 0 := by
      exact norm_ne_zero_iff.mp (by simp [hu_norm])
    have hpu_pos : 0 < p u := map_pos_of_ne_zero p hu_ne
    refine ⟨(p u)⁻¹, inv_pos.mpr hpu_pos, ?_⟩
    intro y
    by_cases hy0 : y = 0
    · simp [hy0]
    · have hy_norm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      let y' : E := ‖y‖⁻¹ • y
      have hy'_sphere : y' ∈ Metric.sphere (0 : E) 1 := by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
        dsimp [y']
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hy_norm_pos.le),
          inv_mul_cancel₀ hy_norm_pos.ne']
      have hu_le : p u ≤ p y' := (isMinOn_iff.mp hu_min) y' hy'_sphere
      have hy'_eq : p y' = ‖y‖⁻¹ * p y := by
        dsimp [y']
        rw [map_smul_eq_mul, Real.norm_of_nonneg (inv_nonneg.mpr hy_norm_pos.le)]
      have htmp : p u ≤ ‖y‖⁻¹ * p y := by
        simpa [hy'_eq] using hu_le
      have hmul : p u * ‖y‖ ≤ p y := by
        simpa [mul_comm] using (le_inv_mul_iff₀ hy_norm_pos).mp htmp
      exact (le_inv_mul_iff₀ hpu_pos).2 hmul

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The pairing image of the closed `p`-unit ball is bounded above, so `p.dualNorm g` is a
genuine real supremum. -/
private theorem bddAbove_innerImage_closedBall
    (p : Seminorm ℝ E) [FiniteDimensional ℝ E] [p.IsNorm] (g : E) :
    BddAbove ((fun x : E ↦ inner ℝ g x) '' p.closedBall 0 1) := by
  obtain ⟨C, hC_pos, hnorm_le⟩ := p.exists_norm_le_mul
  refine ⟨‖g‖ * C, ?_⟩
  rintro z ⟨y, hy, rfl⟩
  have hy_norm : ‖y‖ ≤ C := by
    have hpy : p y ≤ 1 := by
      simpa [Seminorm.mem_closedBall_zero] using hy
    calc
      ‖y‖ ≤ C * p y := hnorm_le y
      _ ≤ C * 1 := by
        gcongr
      _ = C := by
        ring
  calc
    inner ℝ g y ≤ ‖g‖ * ‖y‖ := real_inner_le_norm _ _
    _ ≤ ‖g‖ * C := by
      gcongr


/-- Definition 2.5 in owner form: on a real inner-product space, `p.dualNorm` is the support
function of the closed `p`-unit ball for a separated seminorm `p`, i.e. the textbook dual norm.
The finite-dimensional hypothesis is the canonical owner layer guaranteeing this support value is
an honest real supremum. -/
def dualNorm (p : Seminorm ℝ E) [FiniteDimensional ℝ E] [p.IsNorm] (g : E) : ℝ :=
  sSup ((fun x : E ↦ inner ℝ g x) '' p.closedBall 0 1)

end

end Seminorm

namespace SeminormDualNorm

/- Source-facing Lean notation for the dual norm induced by a separated seminorm `p`. -/
scoped notation:max "‖" g "‖[" p ",*]" => Seminorm.dualNorm p g

end SeminormDualNorm

open scoped SeminormDualNorm

namespace Seminorm

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Expanding the source-facing owner `‖g‖[p,*]` gives the support-function formula over the
closed `p`-unit ball. -/
theorem dualNorm_apply (p : Seminorm ℝ E) [FiniteDimensional ℝ E] [p.IsNorm] (g : E) :
    ‖g‖[p,*] = sSup ((fun x : E ↦ inner ℝ g x) '' {x | p x ≤ 1}) := by
  rw [dualNorm, p.closedBall_zero_eq]

/-- On a finite-dimensional real inner-product space, the dual norm of a separated seminorm is
bounded by a positive constant multiple of the ambient norm. -/
theorem exists_dualNorm_le_mul_norm (p : Seminorm ℝ E) [FiniteDimensional ℝ E] [p.IsNorm] :
    ∃ C > 0, ∀ g : E, ‖g‖[p,*] ≤ C * ‖g‖ := by
  obtain ⟨C, hC_pos, hnorm_le⟩ := p.exists_norm_le_mul
  refine ⟨C, hC_pos, ?_⟩
  intro g
  rw [dualNorm_apply]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⟨0, by simp, by simp⟩⟩
  · rintro y ⟨u, hu, rfl⟩
    have hpu : p u ≤ 1 := hu
    have hu_norm : ‖u‖ ≤ C := by
      calc
        ‖u‖ ≤ C * p u := hnorm_le u
        _ ≤ C * 1 := by
          gcongr
        _ = C := by
          ring
    calc
      inner ℝ g u ≤ ‖g‖ * ‖u‖ := real_inner_le_norm _ _
      _ ≤ ‖g‖ * C := by
        gcongr
      _ = C * ‖g‖ := by
        ring

/-- The dual pairing is bounded by the product of a separated seminorm and its dual norm. -/
theorem inner_le_dualNorm_mul (p : Seminorm ℝ E) [FiniteDimensional ℝ E] [p.IsNorm]
    (x g : E) :
    inner ℝ g x ≤ ‖g‖[p,*] * p x := by
  by_cases hx : x = 0
  · simp [hx, map_zero p]
  · have hpx_pos : 0 < p x := map_pos_of_ne_zero p hx
    let y : E := (p x)⁻¹ • x
    have hy_norm : p y = 1 := by
      simpa [y, Real.norm_of_nonneg (inv_nonneg.mpr hpx_pos.le),
        inv_mul_cancel₀ hpx_pos.ne'] using
        (map_smul_eq_mul p (p x)⁻¹ x)
    have hy_ball : y ∈ p.closedBall 0 1 := by
      rw [Seminorm.mem_closedBall_zero]
      exact hy_norm.le
    have hy_le : inner ℝ g y ≤ ‖g‖[p,*] := by
      rw [dualNorm]
      exact le_csSup (p.bddAbove_innerImage_closedBall g) ⟨y, hy_ball, rfl⟩
    have hx_eq : p x • y = x := by
      simp [y, smul_smul, hpx_pos.ne']
    calc
      inner ℝ g x = inner ℝ g (p x • y) := by rw [hx_eq]
      _ = p x * inner ℝ g y := by rw [real_inner_smul_right]
      _ ≤ p x * ‖g‖[p,*] := mul_le_mul_of_nonneg_left hy_le hpx_pos.le
      _ = ‖g‖[p,*] * p x := by ring

end

end Seminorm

end
