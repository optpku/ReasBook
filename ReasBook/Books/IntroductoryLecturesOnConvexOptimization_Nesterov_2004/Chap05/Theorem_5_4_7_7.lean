/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_18

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter Set Topology
open scoped BigOperators

universe v

variable {ι : Type v} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι
local notation "LPoint" => E × E × ℝ × ℝ

/-- Helper for Theorem 5.4.7.7: package a coordinate function `ι → ℝ` as a vector in
`EuclideanSpace ℝ ι`. -/
private abbrev euclideanVectorOfFun (f : ι → ℝ) : E :=
  (EuclideanSpace.equiv ι ℝ).symm f

/-- Helper for Theorem 5.4.7.7: `euclideanVectorOfFun` has the expected coordinates. -/
@[simp] private theorem euclideanVectorOfFun_apply (f : ι → ℝ) (i : ι) :
    euclideanVectorOfFun (ι := ι) f i = f i := by
  simp [euclideanVectorOfFun]

-- Route repair: this file only needs the source-facing exponential-cone and lifted-cone owners
-- from Definitions 5.4.7.10 and 5.4.7.12. We restate those local formulas here so the current
-- theorem does not depend on the blocked cone-composition import chain through Theorem 5.4.7.6.

/-- Definition 5.4.7.10 (1): the exponential cone consists of the triples `((x, y), τ)` with
`y ≥ τ * exp (x / τ)` and `τ > 0`. -/
def exponentialCone : Set ((ℝ × ℝ) × ℝ)
  | ((x, y), τ) => y ≥ τ * Real.exp (x / τ) ∧ 0 < τ

/-- A triple `((x, y), τ)` belongs to `exponentialCone` exactly when
`y ≥ τ * exp (x / τ)` and `τ > 0`. -/
theorem mem_exponentialCone_iff (x y τ : ℝ) :
    ((x, y), τ) ∈ exponentialCone ↔
      y ≥ τ * Real.exp (x / τ) ∧ 0 < τ :=
  Iff.rfl

/-- Definition 5.4.7.10 (2): the exponential-cone barrier is the textbook logarithmic barrier
`-log (τ log (y / τ) - x) - log y - log τ`. -/
def exponentialConeBarrier : ((ℝ × ℝ) × ℝ) → ℝ
  | ((x, y), τ) => -Real.log (τ * Real.log (y / τ) - x) - Real.log y - Real.log τ

/-- Evaluating `exponentialConeBarrier` at `((x, y), τ)` gives the textbook formula
`-log (τ log (y / τ) - x) - log y - log τ`. -/
theorem exponentialConeBarrier_apply (x y τ : ℝ) :
    exponentialConeBarrier ((x, y), τ) =
      -Real.log (τ * Real.log (y / τ) - x) - Real.log y - Real.log τ :=
  rfl

/-- Definition 5.4.7.12: the lifted cone `hat Q` consists of the quadruples `(x, y, t, τ)` such
that each coordinate triple `((x^(i) - t, y^(i)), τ)` lies in `exponentialCone` and
`∑ i, y^(i) = τ`. -/
def liftedConeLogSumExp : Set LPoint
  | (x, y, t, τ) =>
      (∀ i : ι, ((x i - t, y i), τ) ∈ exponentialCone) ∧
        ∑ i : ι, y i = τ

/-- A quadruple `(x, y, t, τ)` belongs to `liftedConeLogSumExp` exactly when each coordinate
triple `((x^(i) - t, y^(i)), τ)` lies in `exponentialCone` and `∑ i, y^(i) = τ`. -/
theorem mem_liftedConeLogSumExp_iff
    {x y : E} {t τ : ℝ} :
    (x, y, t, τ) ∈ liftedConeLogSumExp ↔
      (∀ i : ι, ((x i - t, y i), τ) ∈ exponentialCone) ∧
        ∑ i : ι, y i = τ :=
  Iff.rfl

/- Theorem 5.4.7.7 lies in the finite-family lifted log-sum-exp / barrier-function domain.

Sampled owner declarations:
* `liftedConeLogSumExp` from `Definition_5_4_7_12`, the source-facing lifted cone owner `hat Q`;
* `exponentialConeBarrier` from `Definition_5_4_7_10`, the scalar logarithmic barrier summed
  coordinatewise in the lifted construction;
* `AffineSubspace`, the canonical ambient owner for the normalization nesterovHyperplane;
* `IsBarrierFunctionOn` from `Chap01/Definition_1_10_18`, the project's canonical barrier owner
  on the intrinsic interior of a closed feasible set.

Source/core/bridge triage:
* source-facing: the nesterovHyperplane restriction of the lifted finite-family barrier `Ψ_L`;
* core/canonical: the normalization affine subspace together with `IsBarrierFunctionOn` on the
  closed normalized feasible region in that relative ambient space;
* bridge/view: the carrier inclusion of the normalization nesterovHyperplane and the resulting restricted
  barrier maps.

Primitive data:
* the finite-family lifted cone `liftedConeLogSumExp`;
* the scalar barrier owner `exponentialConeBarrier`;
* the normalization equation `∑ i, y i = τ`.

Derived API:
* `liftedConeLogSumExpBarrier`;
* `liftedConeLogSumExpNormalizationHyperplane`;
* `liftedConeLogSumExpRelativeDomain`;
* `liftedConeLogSumExpHyperplaneBarrier`;
* `liftedConeLogSumExpRelativeBarrierMap`.

The owner layer stays at an arbitrary finite index type `ι`, matching
`Definition_5_4_7_11` and `Definition_5_4_7_12`; the textbook `Fin n` presentation is only a
specialization bridge. -/

/-- The ambient logarithmic barrier `Ψ_L(x, y, t, τ)` is the finite sum of the canonical scalar
exponential-cone barriers on the coordinate triples `((x^(i) - t, y^(i)), τ)`. -/
def liftedConeLogSumExpBarrier : LPoint → ℝ :=
  fun p ↦ ∑ i : ι, exponentialConeBarrier ((p.1 i - p.2.2.1, p.2.1 i), p.2.2.2)

-- Proof sketch: unfold `liftedConeLogSumExpBarrier`; evaluating at `(x, y, t, τ)` is a direct
-- substitution into the coordinatewise scalar barrier sum.
/-- Evaluating `liftedConeLogSumExpBarrier` at `(x, y, t, τ)` gives the finite sum of the scalar
exponential-cone barriers on the coordinates `((x^(i) - t, y^(i)), τ)`. -/
@[simp]
theorem liftedConeLogSumExpBarrier_apply
    (x y : E) (t τ : ℝ) :
    liftedConeLogSumExpBarrier (x, y, t, τ) =
      ∑ i : ι, exponentialConeBarrier ((x i - t, y i), τ) :=
  rfl

-- Proof sketch: rewrite each summand with `exponentialConeBarrier_apply`, use positivity to
-- expand `log (y^(i) / τ) = log y^(i) - log τ`, and then rearrange the logarithmic slack term.
/-- On the positive branch `τ > 0` and `y^(i) > 0`, the lifted barrier expands to the textbook
formula for `Ψ_L(x, y, t, τ)`. -/
theorem liftedConeLogSumExpBarrier_apply_formula
    (x y : E) (t τ : ℝ) (hτ : 0 < τ) (hy : ∀ i : ι, 0 < y i) :
    liftedConeLogSumExpBarrier (x, y, t, τ) =
      -∑ i : ι,
        (Real.log (t + τ * Real.log (y i) - x i - τ * Real.log τ) +
          Real.log (y i) + Real.log τ) := by
  rw [liftedConeLogSumExpBarrier, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [exponentialConeBarrier_apply]
  have harg :
      τ * Real.log (y i / τ) - (x i - t) =
        t + τ * Real.log (y i) - x i - τ * Real.log τ := by
    rw [Real.log_div (hy i).ne' hτ.ne']
    ring
  rw [harg]
  ring

/-- The linear normalization functional whose kernel cuts out the nesterovHyperplane `∑ i, y i = τ`. -/
private def liftedConeLogSumExpNormalizationLinearMap : LPoint →ₗ[ℝ] ℝ where
  toFun := fun p ↦ ∑ i : ι, p.2.1 i - p.2.2.2
  map_add' p q := by
    simp [Finset.sum_add_distrib, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' c p := by
    simp only [Prod.smul_snd, Prod.smul_fst, PiLp.smul_apply, smul_eq_mul, Real.ringHom_apply,
      sub_eq_add_neg]
    rw [← Finset.mul_sum]
    ring_nf

/-- The normalization nesterovHyperplane `∑ i, y i = τ` on which the relative geometry of `hat Q` is
considered. -/
def liftedConeLogSumExpNormalizationHyperplane : AffineSubspace ℝ LPoint :=
  liftedConeLogSumExpNormalizationLinearMap.ker.toAffineSubspace

local notation "H" => (liftedConeLogSumExpNormalizationHyperplane : AffineSubspace ℝ LPoint)

/-- Helper for Theorem 5.4.7.7: the `i`-th scalar exponential-cone coordinate extracted from a
point of the normalization nesterovHyperplane. -/
def liftedConeLogSumExpCoordinate (i : ι) : H → ((ℝ × ℝ) × ℝ) :=
  fun p ↦ ((p.1.1 i - p.1.2.2.1, p.1.2.1 i), p.1.2.2.2)

-- Proof sketch: the coordinate map just reads off the `i`-th entries of `x` and `y` together
-- with the shared slack variables `(t, τ)` from the underlying quadruple.
/-- Evaluating the `i`-th coordinate map on `(x, y, t, τ)` returns `((x^(i) - t, y^(i)), τ)`. -/
@[simp]
theorem liftedConeLogSumExpCoordinate_apply
    (i : ι) (x y : E) (t τ : ℝ)
    (hxy : (x, y, t, τ) ∈ liftedConeLogSumExpNormalizationHyperplane) :
    liftedConeLogSumExpCoordinate i ⟨(x, y, t, τ), hxy⟩ = ((x i - t, y i), τ) :=
  rfl

-- Proof sketch: every component of the coordinate map is built from continuous projections and
-- arithmetic on the ambient product space, so the resulting map is continuous on the subtype `H`.
/-- Helper for Theorem 5.4.7.7: the ambient `i`-th coordinate extraction map on `LPoint` is
continuous. -/
theorem continuous_liftedConeLogSumExpCoordinateAmbient (i : ι) :
    Continuous (fun p : LPoint ↦ ((p.1 i - p.2.2.1, p.2.1 i), p.2.2.2)) := by
  have hx : Continuous (fun p : LPoint ↦ p.1 i) := by
    simpa using
      (PiLp.continuous_apply (p := 2) (β := fun _ : ι ↦ ℝ) i).comp continuous_fst
  have hy : Continuous (fun p : LPoint ↦ p.2.1 i) := by
    simpa using
      (PiLp.continuous_apply (p := 2) (β := fun _ : ι ↦ ℝ) i).comp
        (continuous_fst.comp continuous_snd)
  have ht : Continuous (fun p : LPoint ↦ p.2.2.1) := by
    simpa using continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hτ : Continuous (fun p : LPoint ↦ p.2.2.2) := by
    simpa using continuous_snd.comp (continuous_snd.comp continuous_snd)
  exact ((hx.sub ht).prodMk hy).prodMk hτ

/-- Helper for Theorem 5.4.7.7: each scalar coordinate map on the normalization nesterovHyperplane is
continuous. -/
theorem continuous_liftedConeLogSumExpCoordinate (i : ι) :
    Continuous (liftedConeLogSumExpCoordinate (ι := ι) i) := by
  simpa [liftedConeLogSumExpCoordinate] using
    (continuous_liftedConeLogSumExpCoordinateAmbient (ι := ι) i).comp continuous_subtype_val

-- Proof sketch: unfold `liftedConeLogSumExpNormalizationHyperplane`; the defining equation is
-- exactly the displayed normalization identity.
/-- A quadruple `(x, y, t, τ)` belongs to the normalization nesterovHyperplane exactly when
`∑ i, y i = τ`. -/
theorem mem_liftedConeLogSumExpNormalizationHyperplane_iff
    {x y : E} {t τ : ℝ} :
    (x, y, t, τ) ∈ liftedConeLogSumExpNormalizationHyperplane ↔ ∑ i, y i = τ := by
  simp [liftedConeLogSumExpNormalizationHyperplane,
    liftedConeLogSumExpNormalizationLinearMap, sub_eq_zero]

/-- The open relative-domain model of `hat Q`, viewed on the carrier of the normalization affine
nesterovHyperplane, is the pullback of the ambient lifted cone along the nesterovHyperplane inclusion. -/
abbrev liftedConeLogSumExpRelativeDomain : Set H :=
  Subtype.val ⁻¹' liftedConeLogSumExp

local notation "D" => (liftedConeLogSumExpRelativeDomain : Set H)

/-- A point of the normalization affine subspace belongs to `liftedConeLogSumExpRelativeDomain`
exactly when its underlying quadruple belongs to the lifted cone `liftedConeLogSumExp`. -/
theorem mem_liftedConeLogSumExpRelativeDomain_iff
    (p : H) :
    p ∈ liftedConeLogSumExpRelativeDomain ↔ p.1 ∈ liftedConeLogSumExp :=
  Iff.rfl

-- Proof sketch: on the normalization nesterovHyperplane, the only nontrivial lifted-cone conditions are
-- the coordinatewise exponential-cone memberships, because the normalization equation is already
-- built into the subtype.
/-- Helper for Theorem 5.4.7.7: on the normalization nesterovHyperplane, belonging to the lifted relative
domain is equivalent to the coordinatewise scalar exponential-cone conditions. -/
theorem mem_liftedConeLogSumExpRelativeDomain_iff_forall_coordinate
    (p : H) :
    p ∈ liftedConeLogSumExpRelativeDomain ↔
      ∀ i : ι, liftedConeLogSumExpCoordinate (ι := ι) i p ∈ exponentialCone := by
  rcases p with ⟨⟨x, y, t, τ⟩, hp⟩
  rw [mem_liftedConeLogSumExpRelativeDomain_iff, mem_liftedConeLogSumExp_iff]
  have hnorm : ∑ i : ι, y i = τ := by
    exact (mem_liftedConeLogSumExpNormalizationHyperplane_iff).1 hp
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, hnorm⟩

/-- The restriction of `Ψ_L` to the normalization nesterovHyperplane `∑ i, y i = τ`. -/
abbrev liftedConeLogSumExpHyperplaneBarrier : H → ℝ :=
  liftedConeLogSumExpBarrier ∘ Subtype.val

-- Proof sketch: unfold `liftedConeLogSumExpHyperplaneBarrier`; it is defined by evaluating the
-- ambient barrier `liftedConeLogSumExpBarrier` on the underlying quadruple.
/-- Evaluating the restricted barrier on the normalization nesterovHyperplane agrees with the ambient
formula `liftedConeLogSumExpBarrier`. -/
theorem liftedConeLogSumExpHyperplaneBarrier_apply
    (p : H) :
    liftedConeLogSumExpHyperplaneBarrier p = liftedConeLogSumExpBarrier p.1 :=
  rfl

-- Proof sketch: the restricted nesterovHyperplane barrier is still the finite sum of the scalar
-- exponential-cone barriers evaluated on the extracted coordinate triples.
/-- Evaluating the nesterovHyperplane-restricted barrier is the sum of the scalar barriers on the
coordinate maps. -/
theorem liftedConeLogSumExpHyperplaneBarrier_eq_sum_coordinates
    (p : H) :
    liftedConeLogSumExpHyperplaneBarrier p =
      ∑ i : ι, exponentialConeBarrier (liftedConeLogSumExpCoordinate (ι := ι) i p) := by
  rcases p with ⟨⟨x, y, t, τ⟩, hp⟩
  change liftedConeLogSumExpBarrier (x, y, t, τ) =
    ∑ i : ι, exponentialConeBarrier ((x i - t, y i), τ)
  rw [liftedConeLogSumExpBarrier_apply]

/-- Helper for Theorem 5.4.7.7: the scalar exponential-cone slack
`y - τ * exp (x / τ)`. -/
private def exponentialConeSlack : ((ℝ × ℝ) × ℝ) → ℝ :=
  fun p ↦ p.1.2 - p.2 * Real.exp (p.1.1 / p.2)

/-- Helper for Theorem 5.4.7.7: the logarithmic slack
`τ * log (y / τ) - x` appearing in `exponentialConeBarrier`. -/
private def exponentialConeBarrierSlack : ((ℝ × ℝ) × ℝ) → ℝ :=
  fun p ↦ p.2 * Real.log (p.1.2 / p.2) - p.1.1

-- Proof sketch: away from `τ = 0`, the scalar slack is assembled from continuous coordinate
-- projections, division, exponentiation, multiplication, and subtraction.
/-- Helper for Theorem 5.4.7.7: the scalar exponential-cone slack is continuous at every point
with nonzero `τ`. -/
private lemma continuousAt_exponentialConeSlack
    {z : ((ℝ × ℝ) × ℝ)} (hzτ : z.2 ≠ 0) :
    ContinuousAt exponentialConeSlack z := by
  have hx : ContinuousAt (fun p : ((ℝ × ℝ) × ℝ) ↦ p.1.1) z :=
    continuous_fst.fst.continuousAt
  have hy : ContinuousAt (fun p : ((ℝ × ℝ) × ℝ) ↦ p.1.2) z :=
    continuous_fst.snd.continuousAt
  have hτ : ContinuousAt (fun p : ((ℝ × ℝ) × ℝ) ↦ p.2) z :=
    continuous_snd.continuousAt
  simpa [exponentialConeSlack] using
    hy.sub (hτ.mul ((Real.continuous_exp.continuousAt).comp (hx.div hτ hzτ)))

/-- Helper for Theorem 5.4.7.7: the logarithmic barrier slack
`τ * log (y / τ) - x` is continuous at points with `τ > 0` and `y > 0`. -/
private lemma continuousAt_exponentialConeBarrierSlack
    {z : ((ℝ × ℝ) × ℝ)} (hτ : 0 < z.2) (hy : 0 < z.1.2) :
    ContinuousAt exponentialConeBarrierSlack z := by
  have hx : ContinuousAt (fun p : ((ℝ × ℝ) × ℝ) ↦ p.1.1) z :=
    continuous_fst.fst.continuousAt
  have hyCont : ContinuousAt (fun p : ((ℝ × ℝ) × ℝ) ↦ p.1.2) z :=
    continuous_fst.snd.continuousAt
  have hτCont : ContinuousAt (fun p : ((ℝ × ℝ) × ℝ) ↦ p.2) z :=
    continuous_snd.continuousAt
  have hdiv : ContinuousAt (fun p : ((ℝ × ℝ) × ℝ) ↦ p.1.2 / p.2) z := by
    exact hyCont.div hτCont hτ.ne'
  have hlog : ContinuousAt (fun p : ((ℝ × ℝ) × ℝ) ↦ Real.log (p.1.2 / p.2)) z := by
    exact hdiv.log (div_ne_zero hy.ne' hτ.ne')
  simpa [exponentialConeBarrierSlack] using (hτCont.mul hlog).sub hx

-- Proof sketch: if a closure point has `τ > 0` but negative slack, continuity gives a whole
-- neighborhood with `τ > 0` and negative slack, which is disjoint from `exponentialCone`.
/-- Helper for Theorem 5.4.7.7: any closure point of `exponentialCone` with positive `τ` still
satisfies the nonnegative scalar slack inequality. -/
private lemma exponentialConeSlack_nonneg_of_mem_closure
    {z : ((ℝ × ℝ) × ℝ)}
    (hz : z ∈ closure exponentialCone) (hτ : 0 < z.2) :
    0 ≤ exponentialConeSlack z := by
  by_contra hneg
  have hcont : ContinuousAt exponentialConeSlack z :=
    continuousAt_exponentialConeSlack hτ.ne'
  have hslack : exponentialConeSlack ⁻¹' Set.Iio 0 ∈ 𝓝 z := by
    exact hcont.preimage_mem_nhds (Iio_mem_nhds (lt_of_not_ge hneg))
  have hτmem : Prod.snd ⁻¹' Set.Ioi (0 : ℝ) ∈ 𝓝 z := by
    exact continuous_snd.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hτ)
  have hneigh : exponentialConeᶜ ∈ 𝓝 z := by
    refine mem_of_superset (inter_mem hτmem hslack) ?_
    intro p hp hpcone
    have hineq := (mem_exponentialCone_iff p.1.1 p.1.2 p.2).1 hpcone
    have hslack_nonneg : 0 ≤ exponentialConeSlack p := by
      dsimp [exponentialConeSlack]
      linarith [hineq.1]
    exact (not_lt_of_ge hslack_nonneg) hp.2
  simpa using (mem_closure_iff_nhds.1 hz) exponentialConeᶜ hneigh

/-- Helper for Theorem 5.4.7.7: any closure point of `exponentialCone` with positive `τ` still
satisfies the nonnegative logarithmic slack inequality `0 ≤ τ * log (y / τ) - x`. -/
private lemma exponentialConeBarrierSlack_nonneg_of_mem_closure
    {z : ((ℝ × ℝ) × ℝ)}
    (hz : z ∈ closure exponentialCone) (hτ : 0 < z.2) :
    0 ≤ exponentialConeBarrierSlack z := by
  have hslack_nonneg : 0 ≤ exponentialConeSlack z :=
    exponentialConeSlack_nonneg_of_mem_closure hz hτ
  have hy : 0 < z.1.2 := by
    have hpos : 0 < z.2 * Real.exp (z.1.1 / z.2) := by
      exact mul_pos hτ (Real.exp_pos _)
    dsimp [exponentialConeSlack] at hslack_nonneg
    linarith
  by_contra hneg
  have hlt : z.2 * Real.log (z.1.2 / z.2) < z.1.1 := by
    dsimp [exponentialConeBarrierSlack] at hneg
    linarith
  have hratio : Real.log (z.1.2 / z.2) < z.1.1 / z.2 := by
    exact (lt_div_iff₀ hτ).2 <| by simpa [mul_comm] using hlt
  have hdiv : z.1.2 / z.2 < Real.exp (z.1.1 / z.2) := by
    exact (Real.log_lt_iff_lt_exp (div_pos hy hτ)).1 hratio
  have hy_lt : z.1.2 < z.2 * Real.exp (z.1.1 / z.2) := by
    simpa [mul_comm] using (div_lt_iff₀ hτ).1 hdiv
  dsimp [exponentialConeSlack] at hslack_nonneg
  linarith

-- Proof sketch: strict positivity of `τ` and of the scalar slack gives neighborhoods on which
-- both inequalities persist, and that neighborhood already lies inside `exponentialCone`.
/-- Helper for Theorem 5.4.7.7: the strict scalar inequalities place a point in
`interior exponentialCone`. -/
private lemma mem_interior_exponentialCone_of_strict
    {x y τ : ℝ} (hτ : 0 < τ) (hslack : τ * Real.exp (x / τ) < y) :
    ((x, y), τ) ∈ interior exponentialCone := by
  rw [mem_interior_iff_mem_nhds]
  have hτmem : Prod.snd ⁻¹' Set.Ioi (0 : ℝ) ∈ 𝓝 ((x, y), τ) := by
    exact continuous_snd.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hτ)
  have hcont : ContinuousAt exponentialConeSlack ((x, y), τ) :=
    continuousAt_exponentialConeSlack hτ.ne'
  have hslackmem : exponentialConeSlack ⁻¹' Set.Ioi (0 : ℝ) ∈ 𝓝 ((x, y), τ) := by
    have hpos : 0 < exponentialConeSlack ((x, y), τ) := by
      dsimp [exponentialConeSlack]
      linarith
    exact hcont.preimage_mem_nhds (Ioi_mem_nhds hpos)
  refine mem_of_superset (inter_mem hτmem hslackmem) ?_
  intro p hp
  rw [mem_exponentialCone_iff]
  constructor
  · have hslack_pos : 0 < exponentialConeSlack p := hp.2
    dsimp [exponentialConeSlack] at hslack_pos
    linarith
  · exact hp.1

-- Proof sketch: the strict scalar inequalities define an open neighborhood already contained in
-- `exponentialCone`, so they certainly lie in `interior (closure exponentialCone)`.
/-- Helper for Theorem 5.4.7.7: the strict scalar inequalities also place a point in
`interior (closure exponentialCone)`. -/
private lemma mem_interior_closure_exponentialCone_of_strict
    {x y τ : ℝ} (hτ : 0 < τ) (hslack : τ * Real.exp (x / τ) < y) :
    ((x, y), τ) ∈ interior (closure exponentialCone) :=
  interior_mono subset_closure (mem_interior_exponentialCone_of_strict hτ hslack)

-- Route correction: the scalar closure theorem can be proved directly from local slack
-- neighborhoods, without importing the blocked Chapter 5 affine-pullback route.
-- Proof sketch: an interior point of `closure exponentialCone` must have `τ > 0`, because the
-- closure is contained in `{τ ≥ 0}`. The slack cannot be zero: shifting `y` slightly downward
-- gives nearby points with negative slack and positive `τ`, hence outside the closure. Therefore
-- the slack is strictly positive, which is exactly the strict exponential-cone inequality.
/-- Helper for Theorem 5.4.7.7: the intrinsic interior of `closure exponentialCone` is exactly the
strict scalar exponential-cone region. -/
private lemma mem_interior_closure_exponentialCone_iff_strict
    (x y τ : ℝ) :
    ((x, y), τ) ∈ interior (closure exponentialCone) ↔
      0 < τ ∧ τ * Real.exp (x / τ) < y := by
  constructor
  · intro hz
    have hsubset : closure exponentialCone ⊆ Prod.snd ⁻¹' (Set.Ici (0 : ℝ)) := by
      refine closure_minimal ?_ ?_
      · intro p hp
        exact le_of_lt ((mem_exponentialCone_iff p.1.1 p.1.2 p.2).1 hp).2
      · simpa using (isClosed_Ici : IsClosed (Set.Ici (0 : ℝ))).preimage continuous_snd
    have hτmem : ((x, y), τ) ∈ Prod.snd ⁻¹' Set.Ioi (0 : ℝ) := by
      have hz' : ((x, y), τ) ∈ interior (Prod.snd ⁻¹' (Set.Ici (0 : ℝ))) :=
        interior_mono hsubset hz
      rw [← isOpenMap_snd.preimage_interior_eq_interior_preimage continuous_snd, interior_Ici] at hz'
      exact hz'
    have hnonneg : 0 ≤ exponentialConeSlack ((x, y), τ) :=
      exponentialConeSlack_nonneg_of_mem_closure (interior_subset hz) hτmem
    have hne : 0 ≠ exponentialConeSlack ((x, y), τ) := by
      intro hzero
      let f : ℝ → ((ℝ × ℝ) × ℝ) := fun r ↦ ((x, y + r), τ)
      have hclosure_zero : (0 : ℝ) ∈ closure (Set.Iio (0 : ℝ)) := by
        simpa [closure_Iio] using (show (0 : ℝ) ∈ Set.Iic (0 : ℝ) from le_rfl)
      have hfcont : ContinuousAt f 0 := by
        have hy : Continuous fun r : ℝ ↦ y + r := continuous_const.add continuous_id
        have hxy : Continuous fun r : ℝ ↦ (x, y + r) := continuous_const.prodMk hy
        have hf : Continuous f := by
          simpa [f] using hxy.prodMk continuous_const
        exact hf.continuousAt
      have hzcomp : ((x, y), τ) ∈ closure (f '' Set.Iio (0 : ℝ)) := by
        have hfwithin : ContinuousWithinAt f (Set.Iio (0 : ℝ)) 0 := hfcont.continuousWithinAt
        simp [f] at hfwithin ⊢
        simpa using hfwithin.mem_closure_image hclosure_zero
      have himage : f '' Set.Iio (0 : ℝ) ⊆ (closure exponentialCone)ᶜ := by
        intro p hp
        rcases hp with ⟨r, hr, rfl⟩
        have hpnot : ¬ (((x, y + r), τ) ∈ closure exponentialCone) := by
          intro hpcl
          have hslack_nonneg : 0 ≤ exponentialConeSlack (((x, y + r), τ)) :=
            exponentialConeSlack_nonneg_of_mem_closure hpcl hτmem
          have hzero' : exponentialConeSlack ((x, y), τ) = 0 := by
            simpa using hzero.symm
          have hslack_r : exponentialConeSlack (((x, y + r), τ)) = r := by
            dsimp [exponentialConeSlack]
            have hbase : y - τ * Real.exp (x / τ) = 0 := by
              simpa [exponentialConeSlack] using hzero'
            linarith
          have hlt : exponentialConeSlack (((x, y + r), τ)) < 0 := by
            simpa [hslack_r] using hr
          exact (not_lt_of_ge hslack_nonneg) hlt
        simpa using hpnot
      have hzcomp' : ((x, y), τ) ∈ closure ((closure exponentialCone)ᶜ) :=
        closure_mono himage hzcomp
      have hinside : closure exponentialCone ∈ 𝓝 ((x, y), τ) := by
        exact mem_of_superset (isOpen_interior.mem_nhds hz) interior_subset
      have : (closure exponentialCone ∩ (closure exponentialCone)ᶜ).Nonempty :=
        (mem_closure_iff_nhds.1 hzcomp') (closure exponentialCone) hinside
      simpa using this
    have hpos : 0 < exponentialConeSlack ((x, y), τ) :=
      lt_of_le_of_ne hnonneg hne
    refine ⟨hτmem, ?_⟩
    dsimp [exponentialConeSlack] at hpos
    linarith
  · rintro ⟨hτ, hslack⟩
    exact mem_interior_closure_exponentialCone_of_strict hτ hslack

-- Proof sketch: `interior exponentialCone` sits inside `interior (closure exponentialCone)`, and
-- the latter has just been identified with the strict scalar inequalities. The reverse direction
-- uses the same strict neighborhood as above directly inside `exponentialCone`.
/-- Helper for Theorem 5.4.7.7: `interior exponentialCone` is exactly the strict scalar
exponential-cone region. -/
private lemma mem_interior_exponentialCone_iff_strict
    (x y τ : ℝ) :
    ((x, y), τ) ∈ interior exponentialCone ↔
      0 < τ ∧ τ * Real.exp (x / τ) < y := by
  constructor
  · intro hz
    exact (mem_interior_closure_exponentialCone_iff_strict x y τ).1
      (interior_mono subset_closure hz)
  · rintro ⟨hτ, hslack⟩
    exact mem_interior_exponentialCone_of_strict hτ hslack

/-- Helper for Theorem 5.4.7.7: the strict coordinatewise exponential-cone slice inside the
normalization nesterovHyperplane. This is the verified open prefix of the intended intrinsic relative
interior description. -/
def liftedConeLogSumExpStrictCoordinateDomain : Set H :=
  ⋂ i : ι,
    {p : H | liftedConeLogSumExpCoordinate (ι := ι) i p ∈ interior exponentialCone}

-- Proof sketch: each coordinate condition is open, and strict coordinatewise feasibility implies
-- ordinary lifted feasibility. Therefore this strict slice is an open subset of the relative
-- domain, hence of `interior (closure D)`.
/-- Helper for Theorem 5.4.7.7: the strict coordinatewise slice is an open subset of
`interior (closure liftedConeLogSumExpRelativeDomain)`. -/
theorem liftedConeLogSumExpStrictCoordinateDomain_subset_interior_closure :
    liftedConeLogSumExpStrictCoordinateDomain (ι := ι) ⊆ interior (closure D) := by
  intro p hp
  have hopen_coord (i : ι) :
      IsOpen {p : H | liftedConeLogSumExpCoordinate (ι := ι) i p ∈ interior exponentialCone} := by
    exact isOpen_interior.preimage (continuous_liftedConeLogSumExpCoordinate (ι := ι) i)
  have hopen :
      IsOpen (liftedConeLogSumExpStrictCoordinateDomain (ι := ι)) := by
    classical
    simpa [liftedConeLogSumExpStrictCoordinateDomain] using
      (isOpen_biInter_finset
        (s := Finset.univ)
        (f := fun i : ι ↦
          {p : H | liftedConeLogSumExpCoordinate (ι := ι) i p ∈ interior exponentialCone})
        (fun i _ ↦ hopen_coord i))
  have hsubset :
      liftedConeLogSumExpStrictCoordinateDomain (ι := ι) ⊆ D := by
    intro q hq
    rw [mem_liftedConeLogSumExpRelativeDomain_iff_forall_coordinate]
    intro i
    exact interior_subset (by
      simpa [liftedConeLogSumExpStrictCoordinateDomain] using
        show q ∈ {p : H | liftedConeLogSumExpCoordinate (ι := ι) i p ∈ interior exponentialCone}
        from by
          exact mem_iInter.1 hq i)
  exact interior_maximal (show liftedConeLogSumExpStrictCoordinateDomain (ι := ι) ⊆ closure D from
      fun q hq ↦ subset_closure (hsubset hq)) hopen hp

/-- Helper for Theorem 5.4.7.7: splitting the finite normalization sum at two distinct indices
isolates the two active coordinates and the untouched remainder. -/
private lemma liftedConeLogSumExp_two_coordinate_sum_split
    [DecidableEq ι] (y : E) {i j : ι} (hij : i ≠ j) :
    y j + (y i + ((Finset.univ.erase j).erase i).sum (fun k ↦ y k)) =
      ∑ k : ι, y k := by
  classical
  have hi_mem_erase : i ∈ (Finset.univ.erase j : Finset ι) := by
    simp [hij]
  calc
    y j + (y i + ((Finset.univ.erase j).erase i).sum (fun k ↦ y k))
        = y j + (Finset.univ.erase j).sum (fun k ↦ y k) := by
            rw [Finset.add_sum_erase (Finset.univ.erase j) (fun k => y k) hi_mem_erase]
    _ = ∑ k : ι, y k := by
          simpa using (Finset.add_sum_erase Finset.univ (fun k => y k) (by simp : j ∈ Finset.univ))

/-- Helper for Theorem 5.4.7.7: the ambient point obtained by replacing one coordinate and one
compensating `y`-coordinate while keeping the normalization equation. -/
private def liftedConeLogSumExpCoordinateSectionAmbient
    [DecidableEq ι] (p : H) (i j : ι) (hij : i ≠ j) :
    ((ℝ × ℝ) × ℝ) → LPoint :=
  fun z ↦
    let x := p.1.1
    let y := p.1.2.1
    let t := p.1.2.2.1
    let rest := ((Finset.univ.erase j).erase i).sum (fun k ↦ y k)
    ( euclideanVectorOfFun (ι := ι) (fun k ↦ if k = i then z.1.1 + t else x k)
    , euclideanVectorOfFun (ι := ι)
        (fun k ↦ if k = i then z.1.2 else if k = j then z.2 - z.1.2 - rest else y k)
    , t
    , z.2 )

/-- Helper for Theorem 5.4.7.7: the compensating-coordinate ambient section still lies in the
normalization nesterovHyperplane. -/
private lemma liftedConeLogSumExpCoordinateSectionAmbient_mem
    [DecidableEq ι] (p : H) (i j : ι) (hij : i ≠ j) (z : ((ℝ × ℝ) × ℝ)) :
    liftedConeLogSumExpCoordinateSectionAmbient (ι := ι) p i j hij z ∈
      liftedConeLogSumExpNormalizationHyperplane := by
  classical
  rcases p with ⟨⟨x, y, t, τ⟩, hp⟩
  have hrest :
      ((Finset.univ.erase j).erase i).sum
          (fun k ↦
            (if k = i then z.1.2
              else if k = j then z.2 - z.1.2 - ((Finset.univ.erase j).erase i).sum (fun l ↦ y l)
              else y k)) =
        ((Finset.univ.erase j).erase i).sum (fun k ↦ y k) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk_ne_i : k ≠ i := (Finset.mem_erase.mp hk).1
    have hk_ne_j : k ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    simp [hk_ne_i, hk_ne_j]
  let y' : E := euclideanVectorOfFun (ι := ι) fun k ↦
    if k = i then z.1.2
    else if k = j then z.2 - z.1.2 - ((Finset.univ.erase j).erase i).sum (fun l ↦ y l)
    else y k
  have hsplit :=
    liftedConeLogSumExp_two_coordinate_sum_split (ι := ι) (y := y') hij
  have hsum_y' :
      ((Finset.univ.erase j).erase i).sum (fun k ↦ y' k) =
        ((Finset.univ.erase j).erase i).sum (fun k ↦ y k) := by
    simpa [y'] using hrest
  have hsum :
      ∑ k : ι,
        (if k = i then z.1.2
          else if k = j then z.2 - z.1.2 - ((Finset.univ.erase j).erase i).sum (fun l ↦ y l)
          else y k) = z.2 := by
    have hleft :
        y' j + (y' i + ((Finset.univ.erase j).erase i).sum (fun k ↦ y' k)) = z.2 := by
      rw [hsum_y']
      simp [y', hij, hij.symm]
    exact hsplit.symm.trans hleft
  simpa [liftedConeLogSumExpCoordinateSectionAmbient,
    mem_liftedConeLogSumExpNormalizationHyperplane_iff] using hsum

/-- Helper for Theorem 5.4.7.7: the compensating-coordinate ambient section is continuous. -/
private lemma continuous_liftedConeLogSumExpCoordinateSectionAmbient
    [DecidableEq ι] (p : H) (i j : ι) (hij : i ≠ j) :
    Continuous (liftedConeLogSumExpCoordinateSectionAmbient (ι := ι) p i j hij) := by
  classical
  rcases p with ⟨⟨x, y, t, τ⟩, hp⟩
  let rest : ℝ := ((Finset.univ.erase j).erase i).sum (fun k ↦ y k)
  have hxFun :
      Continuous fun z : ((ℝ × ℝ) × ℝ) ↦
        (fun k ↦ if k = i then z.1.1 + t else x k) := by
    exact continuous_pi fun k ↦ by
      by_cases hk : k = i
      · subst hk
        simpa using (continuous_fst.fst.add continuous_const)
      · simp [hk]
        simpa using (continuous_const : Continuous fun _ : ((ℝ × ℝ) × ℝ) ↦ x k)
  have hx :
      Continuous fun z : ((ℝ × ℝ) × ℝ) ↦
        euclideanVectorOfFun (ι := ι) (fun k ↦ if k = i then z.1.1 + t else x k) := by
    simpa [euclideanVectorOfFun] using
      (EuclideanSpace.equiv ι ℝ).toHomeomorph.symm.continuous.comp hxFun
  have hyFun :
      Continuous fun z : ((ℝ × ℝ) × ℝ) ↦
        (fun k ↦ if k = i then z.1.2 else if k = j then z.2 - z.1.2 - rest else y k) := by
    exact continuous_pi fun k ↦ by
      by_cases hk : k = i
      · subst hk
        simpa using continuous_fst.snd
      · by_cases hk' : k = j
        · subst hk'
          simpa [hij.symm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, rest] using
            (continuous_snd.sub continuous_fst.snd).sub
              (continuous_const : Continuous fun _ : ((ℝ × ℝ) × ℝ) ↦ rest)
        · simp [hk, hk']
          simpa using (continuous_const : Continuous fun _ : ((ℝ × ℝ) × ℝ) ↦ y k)
  have hy :
      Continuous fun z : ((ℝ × ℝ) × ℝ) ↦
        euclideanVectorOfFun (ι := ι)
          (fun k ↦ if k = i then z.1.2 else if k = j then z.2 - z.1.2 - rest else y k) := by
    simpa [euclideanVectorOfFun] using
      (EuclideanSpace.equiv ι ℝ).toHomeomorph.symm.continuous.comp hyFun
  have htail : Continuous fun z : ((ℝ × ℝ) × ℝ) ↦ ((t, z.2) : ℝ × ℝ) := by
    simpa using (continuous_const.prodMk continuous_snd)
  change Continuous
    (fun z : ((ℝ × ℝ) × ℝ) ↦
      ( euclideanVectorOfFun (ι := ι) (fun k ↦ if k = i then z.1.1 + t else x k)
      , euclideanVectorOfFun (ι := ι)
          (fun k ↦ if k = i then z.1.2 else if k = j then z.2 - z.1.2 - rest else y k)
      , t
      , z.2 ))
  simpa using hx.prodMk (hy.prodMk htail)

/-- Helper for Theorem 5.4.7.7: in the nontrivial index case, each coordinate projection on the
normalization nesterovHyperplane admits a continuous global section obtained by adjusting one compensating
`y`-coordinate to preserve `∑ y = τ`. -/
private lemma liftedConeLogSumExpCoordinate_has_global_section
    [Nontrivial ι] (p : H) (i : ι) :
    ∃ s : ((ℝ × ℝ) × ℝ) → H,
      Continuous s ∧
      s (liftedConeLogSumExpCoordinate (ι := ι) i p) = p ∧
      ∀ z : ((ℝ × ℝ) × ℝ),
        liftedConeLogSumExpCoordinate (ι := ι) i (s z) = z := by
  classical
  obtain ⟨j, hij⟩ := exists_ne i
  have hij' : i ≠ j := hij.symm
  let s : ((ℝ × ℝ) × ℝ) → H := fun z ↦
    ⟨liftedConeLogSumExpCoordinateSectionAmbient (ι := ι) p i j hij' z,
      liftedConeLogSumExpCoordinateSectionAmbient_mem (ι := ι) p i j hij' z⟩
  refine ⟨s, ?_, ?_, ?_⟩
  · -- The section is continuous because the ambient replacement map is coordinatewise continuous.
    have hs :
        Continuous (liftedConeLogSumExpCoordinateSectionAmbient (ι := ι) p i j hij') :=
      continuous_liftedConeLogSumExpCoordinateSectionAmbient (ι := ι) p i j hij'
    simpa [s] using Continuous.subtype_mk hs
      (liftedConeLogSumExpCoordinateSectionAmbient_mem (ι := ι) p i j hij')
  · -- Evaluating the section at the original coordinate reconstructs the original point.
    rcases p with ⟨⟨x, y, t, τ⟩, hp⟩
    have hnorm : ∑ k : ι, y k = τ :=
      (mem_liftedConeLogSumExpNormalizationHyperplane_iff).1 hp
    have hsplit :=
      liftedConeLogSumExp_two_coordinate_sum_split (ι := ι) (y := y) hij'
    have hyj :
        τ - y i - ((Finset.univ.erase j).erase i).sum (fun k ↦ y k) = y j := by
      have hsum' : y j + (y i + ((Finset.univ.erase j).erase i).sum (fun k ↦ y k)) = τ := by
        simpa [hnorm] using hsplit
      linarith
    ext k
    · by_cases hk : k = i
      · subst hk
        simp [s, liftedConeLogSumExpCoordinateSectionAmbient]
      · simp [s, liftedConeLogSumExpCoordinateSectionAmbient, hk]
    · by_cases hk : k = i
      · subst hk
        simp [s, liftedConeLogSumExpCoordinateSectionAmbient]
      · by_cases hk' : k = j
        · subst hk'
          simp [s, liftedConeLogSumExpCoordinateSectionAmbient, hij, hyj]
        · simp [s, liftedConeLogSumExpCoordinateSectionAmbient, hk, hk']
    · simp [s, liftedConeLogSumExpCoordinateSectionAmbient]
    · simp [s, liftedConeLogSumExpCoordinateSectionAmbient]
  · -- The chosen coordinate is read back exactly, by construction of the section.
    intro z
    simp [s, liftedConeLogSumExpCoordinateSectionAmbient, hij']

/-- Helper for Theorem 5.4.7.7: every point of `closure D` has each scalar coordinate in
`closure exponentialCone`. -/
private lemma liftedConeLogSumExpCoordinate_mem_closure_of_mem_closure
    {p : H} (hp : p ∈ closure D) (i : ι) :
    liftedConeLogSumExpCoordinate (ι := ι) i p ∈ closure exponentialCone := by
  have hsubset :
      D ⊆ liftedConeLogSumExpCoordinate (ι := ι) i ⁻¹' closure exponentialCone := by
    intro q hq
    rw [mem_preimage]
    exact subset_closure <|
      (mem_liftedConeLogSumExpRelativeDomain_iff_forall_coordinate (ι := ι) q).1 hq i
  have hclosed :
      IsClosed (liftedConeLogSumExpCoordinate (ι := ι) i ⁻¹' closure exponentialCone) :=
    isClosed_closure.preimage (continuous_liftedConeLogSumExpCoordinate (ι := ι) i)
  exact (closure_minimal hsubset hclosed hp)

/-- Helper for Theorem 5.4.7.7: every point of the intrinsic interior of the closed normalized
lifted cone has each scalar coordinate in `interior (closure exponentialCone)`. -/
private lemma liftedConeLogSumExpCoordinate_mem_interior_closure_of_mem_interior_closure
    {p : H} (hp : p ∈ interior (closure D)) (i : ι) :
    liftedConeLogSumExpCoordinate (ι := ι) i p ∈ interior (closure exponentialCone) := by
  classical
  by_cases hsub : Subsingleton ι
  · let z0 := liftedConeLogSumExpCoordinate (ι := ι) i p
    have hz0_closure : z0 ∈ closure exponentialCone :=
      liftedConeLogSumExpCoordinate_mem_closure_of_mem_closure (ι := ι) (interior_subset hp) i
    rcases p with ⟨⟨x, y, t, τ⟩, hpH⟩
    have hsum : ∑ k : ι, y k = τ :=
      (mem_liftedConeLogSumExpNormalizationHyperplane_iff).1 hpH
    have huniv : (Finset.univ : Finset ι) = {i} := by
      ext k
      simp [hsub.elim k i]
    have hy_eq : y i = τ := by
      simpa [huniv] using hsum
    have hτ_nonneg_on_D : D ⊆ {q : H | 0 ≤ q.1.2.2.2} := by
      intro q hq
      have hmem :
          liftedConeLogSumExpCoordinate (ι := ι) i q ∈ exponentialCone :=
        (mem_liftedConeLogSumExpRelativeDomain_iff_forall_coordinate (ι := ι) q).1 hq i
      exact le_of_lt ((mem_exponentialCone_iff _ _ _).1 hmem).2
    have hτ_nonneg_set :
        closure D ⊆ {q : H | 0 ≤ q.1.2.2.2} := by
      have hclosed : IsClosed {q : H | 0 ≤ q.1.2.2.2} := by
        simpa using
          (isClosed_Ici : IsClosed (Set.Ici (0 : ℝ))).preimage
            (show Continuous fun q : H ↦ q.1.2.2.2 by
              simpa using
                (continuous_snd.comp
                  (continuous_snd.comp
                    (continuous_snd.comp continuous_subtype_val))))
      exact closure_minimal hτ_nonneg_on_D hclosed
    have hτ_mem : τ ∈ interior (Set.Ici (0 : ℝ)) := by
      let τSectionAmbient : ℝ → LPoint := fun c ↦
        (euclideanVectorOfFun (ι := ι) fun k ↦ x k, euclideanVectorOfFun (ι := ι) fun _ ↦ c, t, c)
      have hτSection_mem :
          ∀ c : ℝ, τSectionAmbient c ∈ liftedConeLogSumExpNormalizationHyperplane := by
        intro c
        simpa [τSectionAmbient, mem_liftedConeLogSumExpNormalizationHyperplane_iff, huniv]
      let τSection : ℝ → H := fun c ↦ ⟨τSectionAmbient c, hτSection_mem c⟩
      have hτSectionAmbient_cont : Continuous τSectionAmbient := by
        have hxcont : Continuous fun c : ℝ ↦ euclideanVectorOfFun (ι := ι) fun k ↦ x k := by
          simpa [euclideanVectorOfFun] using
            (EuclideanSpace.equiv ι ℝ).toHomeomorph.symm.continuous.comp continuous_const
        have hyFun : Continuous fun c : ℝ ↦ (fun _ : ι ↦ c) := by
          exact continuous_pi fun k ↦ by
            simpa using continuous_id
        have hycont : Continuous fun c : ℝ ↦ euclideanVectorOfFun (ι := ι) fun _ : ι ↦ c := by
          simpa [euclideanVectorOfFun] using
            (EuclideanSpace.equiv ι ℝ).toHomeomorph.symm.continuous.comp hyFun
        simpa [τSectionAmbient] using
          hxcont.prodMk (hycont.prodMk (continuous_const.prodMk continuous_id))
      have hτSection_cont : Continuous τSection := by
        simpa [τSection] using Continuous.subtype_mk hτSectionAmbient_cont hτSection_mem
      have hτSection_eq : τSection τ = (⟨(x, y, t, τ), hpH⟩ : H) := by
        ext k
        · simp [τSection, τSectionAmbient]
        · have hk : k = i := hsub.elim k i
          subst hk
          simp [τSection, τSectionAmbient, hy_eq]
        · simp [τSection, τSectionAmbient]
        · simp [τSection, τSectionAmbient]
      rw [mem_interior_iff_mem_nhds]
      have hpnhds : closure D ∈ 𝓝 (⟨(x, y, t, τ), hpH⟩ : H) :=
        (mem_interior_iff_mem_nhds).1 hp
      have hpre :
          τSection ⁻¹' closure D ∈ 𝓝 τ := by
        have hbase : closure D ∈ 𝓝 (τSection τ) := by
          simpa [hτSection_eq] using hpnhds
        exact hτSection_cont.continuousAt.preimage_mem_nhds hbase
      refine mem_of_superset hpre ?_
      intro c hc
      simpa [τSection, τSectionAmbient] using hτ_nonneg_set hc
    have hτ : 0 < τ := by
      simpa [interior_Ici] using hτ_mem
    have hdiff_nonpos_on_D : D ⊆ {q : H | q.1.1 i - q.1.2.2.1 ≤ 0} := by
      intro q hq
      have hmem :
          liftedConeLogSumExpCoordinate (ι := ι) i q ∈ exponentialCone :=
        (mem_liftedConeLogSumExpRelativeDomain_iff_forall_coordinate (ι := ι) q).1 hq i
      have hτq : 0 < q.1.2.2.2 := ((mem_exponentialCone_iff _ _ _).1 hmem).2
      have hyq_eq : q.1.2.1 i = q.1.2.2.2 := by
        have hsumq :
            ∑ k : ι, q.1.2.1 k = q.1.2.2.2 :=
          (mem_liftedConeLogSumExpNormalizationHyperplane_iff).1 q.2
        simpa [huniv] using hsumq
      have hineq :
          q.1.2.1 i ≥ q.1.2.2.2 * Real.exp ((q.1.1 i - q.1.2.2.1) / q.1.2.2.2) :=
        ((mem_exponentialCone_iff _ _ _).1 hmem).1
      rw [hyq_eq] at hineq
      have hexp_le_one :
          Real.exp ((q.1.1 i - q.1.2.2.1) / q.1.2.2.2) ≤ 1 := by
        have hineq' :
            q.1.2.2.2 * Real.exp ((q.1.1 i - q.1.2.2.1) / q.1.2.2.2) ≤ q.1.2.2.2 := by
          simpa using hineq
        have hdiv :
            Real.exp ((q.1.1 i - q.1.2.2.1) / q.1.2.2.2) ≤ q.1.2.2.2 / q.1.2.2.2 := by
          exact (le_div_iff₀ hτq).2 <| by simpa [mul_comm] using hineq'
        simpa [hτq.ne'] using hdiv
      have hdiv_le_zero :
          (q.1.1 i - q.1.2.2.1) / q.1.2.2.2 ≤ 0 :=
        (Real.exp_le_one_iff).1 hexp_le_one
      have hnum :
          q.1.1 i - q.1.2.2.1 ≤ 0 := by
        have := (div_le_iff₀ hτq).1 hdiv_le_zero
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      exact hnum
    have hdiff_nonpos_set :
        closure D ⊆ {q : H | q.1.1 i - q.1.2.2.1 ≤ 0} := by
      exact closure_minimal hdiff_nonpos_on_D <|
        (isClosed_Iic : IsClosed (Set.Iic (0 : ℝ))).preimage <|
          ((PiLp.continuous_apply (p := 2) (β := fun _ : ι ↦ ℝ) i).comp
              (continuous_fst.comp continuous_subtype_val)).sub
            (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)))
    have hdiff_mem : x i - t ∈ interior (Set.Iic (0 : ℝ)) := by
      let diffSectionAmbient : ℝ → LPoint := fun a ↦
        (euclideanVectorOfFun (ι := ι) fun _ ↦ a + t, euclideanVectorOfFun (ι := ι) fun _ ↦ τ, t, τ)
      have hdiffSection_mem :
          ∀ a : ℝ, diffSectionAmbient a ∈ liftedConeLogSumExpNormalizationHyperplane := by
        intro a
        simpa [diffSectionAmbient, mem_liftedConeLogSumExpNormalizationHyperplane_iff, huniv]
      let diffSection : ℝ → H := fun a ↦ ⟨diffSectionAmbient a, hdiffSection_mem a⟩
      have hdiffSectionAmbient_cont : Continuous diffSectionAmbient := by
        have hxFun : Continuous fun a : ℝ ↦ (fun _ : ι ↦ a + t) := by
          exact continuous_pi fun k ↦ by
            simpa using (continuous_id.add continuous_const)
        have hxcont : Continuous fun a : ℝ ↦ euclideanVectorOfFun (ι := ι) fun _ : ι ↦ a + t := by
          simpa [euclideanVectorOfFun] using
            (EuclideanSpace.equiv ι ℝ).toHomeomorph.symm.continuous.comp hxFun
        have hyFun : Continuous fun _ : ℝ ↦ (fun _ : ι ↦ τ) := by
          exact continuous_pi fun k ↦ by
            simpa using (continuous_const : Continuous fun _ : ℝ ↦ τ)
        have hycont : Continuous fun a : ℝ ↦ euclideanVectorOfFun (ι := ι) fun _ : ι ↦ τ := by
          simpa [euclideanVectorOfFun] using
            (EuclideanSpace.equiv ι ℝ).toHomeomorph.symm.continuous.comp hyFun
        simpa [diffSectionAmbient] using
          hxcont.prodMk (hycont.prodMk (continuous_const.prodMk continuous_const))
      have hdiffSection_cont : Continuous diffSection := by
        simpa [diffSection] using Continuous.subtype_mk hdiffSectionAmbient_cont hdiffSection_mem
      have hdiffSection_eq : diffSection (x i - t) = (⟨(x, y, t, τ), hpH⟩ : H) := by
        ext k
        · have hk : k = i := hsub.elim k i
          subst hk
          simp [diffSection, diffSectionAmbient]
        · have hk : k = i := hsub.elim k i
          subst hk
          simp [diffSection, diffSectionAmbient, hy_eq]
        · simp [diffSection, diffSectionAmbient]
        · simp [diffSection, diffSectionAmbient]
      rw [mem_interior_iff_mem_nhds]
      have hpnhds : closure D ∈ 𝓝 (⟨(x, y, t, τ), hpH⟩ : H) :=
        (mem_interior_iff_mem_nhds).1 hp
      have hpre :
          diffSection ⁻¹' closure D ∈ 𝓝 (x i - t) := by
        have hbase : closure D ∈ 𝓝 (diffSection (x i - t)) := by
          simpa [hdiffSection_eq] using hpnhds
        exact hdiffSection_cont.continuousAt.preimage_mem_nhds hbase
      refine mem_of_superset hpre ?_
      intro a ha
      simpa [diffSection, diffSectionAmbient] using hdiff_nonpos_set ha
    have hdiff_lt : x i - t < 0 := by
      simpa [interior_Iic] using hdiff_mem
    have hdiv_lt_zero : (x i - t) / τ < 0 := by
      have : x i - t < 0 * τ := by
        simpa using hdiff_lt
      exact (div_lt_iff₀ hτ).2 this
    have hexp_lt_one : Real.exp ((x i - t) / τ) < 1 := by
      exact (Real.exp_lt_one_iff).2 hdiv_lt_zero
    have hstrict : τ * Real.exp ((x i - t) / τ) < y i := by
      have hmul : τ * Real.exp ((x i - t) / τ) < τ := by
        simpa [mul_comm] using (mul_lt_mul_of_pos_left hexp_lt_one hτ)
      simpa [hy_eq] using hmul
    simpa [z0, hy_eq] using
      (mem_interior_closure_exponentialCone_iff_strict (x i - t) (y i) τ).2 ⟨hτ, hstrict⟩
  · have hnontrivial : Nontrivial ι := not_subsingleton_iff_nontrivial.1 hsub
    letI := hnontrivial
    let z0 := liftedConeLogSumExpCoordinate (ι := ι) i p
    obtain ⟨s, hscont, hsp, hscoord⟩ :=
      liftedConeLogSumExpCoordinate_has_global_section (ι := ι) p i
    rw [mem_interior_iff_mem_nhds]
    have hpnhds : closure D ∈ 𝓝 p := (mem_interior_iff_mem_nhds).1 hp
    have hpre : s ⁻¹' closure D ∈ 𝓝 z0 := by
      have hbase : closure D ∈ 𝓝 (s z0) := by simpa [z0, hsp] using hpnhds
      exact hscont.continuousAt.preimage_mem_nhds hbase
    refine mem_of_superset hpre ?_
    intro z hz
    have hsz : s z ∈ closure D := hz
    have hcoord_closure :
        liftedConeLogSumExpCoordinate (ι := ι) i (s z) ∈ closure exponentialCone :=
      liftedConeLogSumExpCoordinate_mem_closure_of_mem_closure (ι := ι) hsz i
    simpa [hscoord z] using hcoord_closure

/-- Helper for Theorem 5.4.7.7: the intrinsic interior of the closed normalized lifted cone is
exactly the strict coordinatewise exponential-cone slice on the normalization nesterovHyperplane. -/
private lemma mem_interior_closure_liftedConeLogSumExpRelativeDomain_iff_strict_coordinates
    (p : H) :
    p ∈ interior (closure D) ↔
      p ∈ liftedConeLogSumExpStrictCoordinateDomain (ι := ι) := by
  constructor
  · intro hp
    rw [liftedConeLogSumExpStrictCoordinateDomain]
    refine mem_iInter.2 ?_
    intro i
    have hcoord :
        liftedConeLogSumExpCoordinate (ι := ι) i p ∈ interior (closure exponentialCone) :=
      liftedConeLogSumExpCoordinate_mem_interior_closure_of_mem_interior_closure
        (ι := ι) hp i
    rcases hzi : liftedConeLogSumExpCoordinate (ι := ι) i p with ⟨⟨x, y⟩, τ⟩
    have hstrict :
        0 < τ ∧ τ * Real.exp (x / τ) < y :=
      (mem_interior_closure_exponentialCone_iff_strict x y τ).1 (by simpa [hzi] using hcoord)
    simpa [hzi] using (mem_interior_exponentialCone_iff_strict x y τ).2 hstrict
  · intro hpstrict
    exact liftedConeLogSumExpStrictCoordinateDomain_subset_interior_closure (ι := ι) hpstrict

/-- Helper for Theorem 5.4.7.7: the scalar exponential-cone barrier is continuous on the strict
interior of the exponential cone. -/
private lemma continuousOn_exponentialConeBarrier_interior :
    ContinuousOn exponentialConeBarrier (interior exponentialCone) := by
  intro z hz
  rcases z with ⟨⟨x, y⟩, τ⟩
  rcases (mem_interior_exponentialCone_iff_strict x y τ).1 hz with ⟨hτ, hslack⟩
  have hy : 0 < y := by
    -- Strict exponential-cone slack forces the logarithm argument `y` to stay positive.
    exact lt_trans (mul_pos hτ (Real.exp_pos (x / τ))) hslack
  have hy_div : 0 < y / τ := div_pos hy hτ
  have hdiv : Real.exp (x / τ) < y / τ := by
    -- Divide the strict slack inequality by the positive scalar `τ`.
    exact (lt_div_iff₀ hτ).2 (by simpa [mul_comm] using hslack)
  have hlog : x / τ < Real.log (y / τ) := (Real.lt_log_iff_exp_lt hy_div).2 hdiv
  have harg : 0 < τ * Real.log (y / τ) - x := by
    -- Transport the strict logarithmic inequality back to the barrier slack.
    have hxlt : x < τ * Real.log (y / τ) := by
      simpa [mul_comm] using (div_lt_iff₀ hτ).1 hlog
    linarith
  let xArg : ((ℝ × ℝ) × ℝ) → ℝ := fun p ↦ p.1.1
  let yArg : ((ℝ × ℝ) × ℝ) → ℝ := fun p ↦ p.1.2
  let τArg : ((ℝ × ℝ) × ℝ) → ℝ := fun p ↦ p.2
  let divArg : ((ℝ × ℝ) × ℝ) → ℝ := fun p ↦ yArg p / τArg p
  let slackArg : ((ℝ × ℝ) × ℝ) → ℝ := fun p ↦ τArg p * Real.log (divArg p) - xArg p
  let barrierExpr : ((ℝ × ℝ) × ℝ) → ℝ := fun p ↦
    -Real.log (slackArg p) - Real.log (yArg p) - Real.log (τArg p)
  have hx : ContinuousAt xArg ((x, y), τ) := by
    simpa [xArg] using (continuous_fst.fst.continuousAt : ContinuousAt (fun p : ((ℝ × ℝ) × ℝ) ↦ p.1.1) ((x, y), τ))
  have hyCont : ContinuousAt yArg ((x, y), τ) := by
    simpa [yArg] using (continuous_fst.snd.continuousAt : ContinuousAt (fun p : ((ℝ × ℝ) × ℝ) ↦ p.1.2) ((x, y), τ))
  have hτCont : ContinuousAt τArg ((x, y), τ) := by
    simpa [τArg] using (continuous_snd.continuousAt : ContinuousAt (fun p : ((ℝ × ℝ) × ℝ) ↦ p.2) ((x, y), τ))
  have hdivCont : ContinuousAt divArg ((x, y), τ) := by
    simpa [divArg] using hyCont.div hτCont hτ.ne'
  have hlogAt : ContinuousAt Real.log (divArg ((x, y), τ)) := by
    simpa [divArg, yArg, τArg] using
      (Real.continuousAt_log (div_ne_zero hy.ne' hτ.ne') : ContinuousAt Real.log (y / τ))
  have hlogCont : ContinuousAt (Real.log ∘ divArg) ((x, y), τ) := by
    simpa [Function.comp] using hlogAt.comp hdivCont
  have hslackCont : ContinuousAt slackArg ((x, y), τ) := by
    simpa [slackArg, xArg, τArg, Function.comp] using (hτCont.mul hlogCont).sub hx
  have hslackLogAt : ContinuousAt Real.log (slackArg ((x, y), τ)) := by
    simpa [slackArg, xArg, yArg, τArg, divArg] using
      (Real.continuousAt_log (ne_of_gt harg) :
        ContinuousAt Real.log (τ * Real.log (y / τ) - x))
  have hyLogAt : ContinuousAt Real.log (yArg ((x, y), τ)) := by
    simpa [yArg] using (Real.continuousAt_log hy.ne' : ContinuousAt Real.log y)
  have hτLogAt : ContinuousAt Real.log (τArg ((x, y), τ)) := by
    simpa [τArg] using (Real.continuousAt_log hτ.ne' : ContinuousAt Real.log τ)
  have hyLogCont : ContinuousAt (Real.log ∘ yArg) ((x, y), τ) := by
    simpa [Function.comp] using hyLogAt.comp hyCont
  have hτLogCont : ContinuousAt (Real.log ∘ τArg) ((x, y), τ) := by
    simpa [Function.comp] using hτLogAt.comp hτCont
  have hmodel : ContinuousAt barrierExpr ((x, y), τ) := by
    -- Each logarithm is continuous because its argument is strictly positive on the interior.
    simpa [barrierExpr, slackArg, xArg, yArg, τArg, divArg, Function.comp] using
      ((hslackLogAt.comp hslackCont).neg.sub hyLogCont).sub hτLogCont
  have hformula :
      exponentialConeBarrier =
        barrierExpr := by
    funext p
    rcases p with ⟨⟨x', y'⟩, τ'⟩
    simp [barrierExpr, slackArg, xArg, yArg, τArg, divArg, exponentialConeBarrier_apply]
  simpa [hformula] using hmodel.continuousWithinAt

/-- The canonical bundled barrier map on the intrinsic interior of the closed normalized lifted
region `closure liftedConeLogSumExpRelativeDomain`, obtained by restricting the nesterovHyperplane bridge
once more to the intrinsic interior. -/
abbrev liftedConeLogSumExpRelativeBarrierMap :
    C(interior (closure D), ℝ) where
  toFun := (interior (closure D)).restrict
    liftedConeLogSumExpHyperplaneBarrier
  -- Route correction: first identify `interior (closure D)` with the strict coordinate slice on
  -- `H`, then read continuity coordinatewise from the scalar exponential-cone barrier.
  continuous_toFun := by
    have hcoord_mem :
        ∀ p : interior (closure D), ∀ i : ι,
          liftedConeLogSumExpCoordinate (ι := ι) i p.1 ∈ interior exponentialCone := by
      intro p i
      have hpstrict :
          p.1 ∈ liftedConeLogSumExpStrictCoordinateDomain (ι := ι) :=
        (mem_interior_closure_liftedConeLogSumExpRelativeDomain_iff_strict_coordinates
          (ι := ι) p.1).1 p.2
      simpa [liftedConeLogSumExpStrictCoordinateDomain] using mem_iInter.1 hpstrict i
    have hsum :
        Continuous fun p : interior (closure D) ↦
          ∑ i : ι, exponentialConeBarrier (liftedConeLogSumExpCoordinate (ι := ι) i p.1) := by
      classical
      have hsummand (i : ι) :
          Continuous fun p : interior (closure D) ↦
            exponentialConeBarrier (liftedConeLogSumExpCoordinate (ι := ι) i p.1) := by
        refine continuous_iff_continuousAt.2 ?_
        intro p
        have hz : liftedConeLogSumExpCoordinate (ι := ι) i p.1 ∈ interior exponentialCone :=
          hcoord_mem p i
        have hbar :
            ContinuousAt exponentialConeBarrier
              (liftedConeLogSumExpCoordinate (ι := ι) i p.1) :=
          continuousOn_exponentialConeBarrier_interior.continuousAt
            (isOpen_interior.mem_nhds hz)
        have hcoordCont :
            Continuous fun p : interior (closure D) ↦
              liftedConeLogSumExpCoordinate (ι := ι) i p.1 :=
          (continuous_liftedConeLogSumExpCoordinate (ι := ι) i).comp continuous_subtype_val
        let coordOnInterior : interior (closure D) → ((ℝ × ℝ) × ℝ) :=
          fun q ↦ liftedConeLogSumExpCoordinate (ι := ι) i q.1
        have hcoordAt : ContinuousAt coordOnInterior p := by
          simpa [coordOnInterior] using hcoordCont.continuousAt
        have hbar' : ContinuousAt exponentialConeBarrier (coordOnInterior p) := by
          simpa [coordOnInterior] using hbar
        exact hbar'.comp hcoordAt
      simpa using continuous_finset_sum Finset.univ (fun i _ ↦ hsummand i)
    simpa [liftedConeLogSumExpHyperplaneBarrier_eq_sum_coordinates] using hsum

/-- Evaluating the canonical bundled barrier map agrees with the ambient nesterovHyperplane restriction. -/
theorem liftedConeLogSumExpRelativeBarrierMap_apply
    (p : interior (closure D)) :
    liftedConeLogSumExpRelativeBarrierMap p = liftedConeLogSumExpHyperplaneBarrier p.1 :=
  rfl

/-- Helper for Theorem 5.4.7.7: every closure point of the scalar exponential cone has
nonnegative `τ`. -/
private lemma exponentialCone_tau_nonneg_of_mem_closure
    {z : ((ℝ × ℝ) × ℝ)} (hz : z ∈ closure exponentialCone) :
    0 ≤ z.2 := by
  -- The scalar cone is contained in the closed half-space `τ ≥ 0`, and closedness passes to the
  -- closure.
  have hsubset : closure exponentialCone ⊆ Prod.snd ⁻¹' Set.Ici (0 : ℝ) := by
    refine closure_minimal ?_ ?_
    · intro p hp
      exact le_of_lt ((mem_exponentialCone_iff p.1.1 p.1.2 p.2).1 hp).2
    · simpa using (isClosed_Ici : IsClosed (Set.Ici (0 : ℝ))).preimage continuous_snd
  exact hsubset hz

/-- Helper for Theorem 5.4.7.7: the strict coordinatewise slice of the normalized lifted cone is
nonempty. -/
private lemma liftedConeLogSumExpStrictCoordinateDomain_nonempty :
    (liftedConeLogSumExpStrictCoordinateDomain (ι := ι)).Nonempty := by
  classical
  by_cases hι : IsEmpty ι
  · let p0 : LPoint := (0, 0, 0, 0)
    have hp0H : p0 ∈ liftedConeLogSumExpNormalizationHyperplane := by
      rw [mem_liftedConeLogSumExpNormalizationHyperplane_iff]
      simp [isEmpty_iff.mp hι]
    let p : H := ⟨p0, hp0H⟩
    refine ⟨p, ?_⟩
    -- With no coordinates, the strict intersection is the whole nesterovHyperplane.
    simp [liftedConeLogSumExpStrictCoordinateDomain, isEmpty_iff.mp hι]
  · letI : Nonempty ι := not_isEmpty_iff.mp hι
    let τ : ℝ := Fintype.card ι
    let x : E := 0
    let y : E := euclideanVectorOfFun (ι := ι) fun _ ↦ 1
    let t : ℝ := τ ^ 2
    have hτ : 0 < τ := by
      dsimp [τ]
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    have hsum : ∑ i : ι, y i = τ := by
      simp [y, τ]
    have hpH : (x, y, t, τ) ∈ liftedConeLogSumExpNormalizationHyperplane := by
      exact (mem_liftedConeLogSumExpNormalizationHyperplane_iff).2 hsum
    let p : H := ⟨(x, y, t, τ), hpH⟩
    refine ⟨p, ?_⟩
    -- Each coordinate has positive `τ` and positive slack `1 - τ * exp (-τ)`.
    rw [liftedConeLogSumExpStrictCoordinateDomain]
    refine mem_iInter.2 ?_
    intro i
    have hratio : (x i - t) / τ = -τ := by
      dsimp [x, t]
      field_simp [hτ.ne']
      ring
    have hcard_lt_exp : τ < Real.exp τ := by
      have hexp := Real.add_one_lt_exp hτ.ne'
      linarith
    have hslack : τ * Real.exp ((x i - t) / τ) < y i := by
      have hdiv : τ / Real.exp τ < 1 := by
        exact (div_lt_one (Real.exp_pos τ)).2 hcard_lt_exp
      simpa [y, hratio, div_eq_mul_inv, Real.exp_neg, mul_comm, mul_left_comm, mul_assoc]
        using hdiv
    exact mem_interior_exponentialCone_of_strict hτ hslack

/-- Helper for Theorem 5.4.7.7: a frontier point of the normalized lifted cone has at least one
scalar coordinate on the frontier of `closure exponentialCone`. -/
private lemma
    exists_coordinate_mem_frontier_closure_exponentialCone_of_mem_frontier_closure_liftedConeLogSumExpRelativeDomain
    [Nonempty ι] {pBar : H} (hpBar : pBar ∈ frontier (closure D)) :
    ∃ i : ι, liftedConeLogSumExpCoordinate (ι := ι) i pBar ∈ frontier (closure exponentialCone) := by
  classical
  have hpBar_mem : pBar ∈ closure D := by
    simpa [frontier, closure_closure] using hpBar.1
  have hpBar_not_int : pBar ∉ interior (closure D) := by
    simpa [frontier, closure_closure] using hpBar.2
  by_contra hnone
  have hcoord_int :
      ∀ i : ι, liftedConeLogSumExpCoordinate (ι := ι) i pBar ∈ interior (closure exponentialCone) := by
    intro i
    have hcoord_mem :
        liftedConeLogSumExpCoordinate (ι := ι) i pBar ∈ closure exponentialCone :=
      liftedConeLogSumExpCoordinate_mem_closure_of_mem_closure (ι := ι) hpBar_mem i
    have hnot_front :
        liftedConeLogSumExpCoordinate (ι := ι) i pBar ∉ frontier (closure exponentialCone) := by
      exact not_exists.mp hnone i
    exact (mem_interior_iff_notMem_frontier hcoord_mem).2 hnot_front
  have hpBar_strict :
      pBar ∈ liftedConeLogSumExpStrictCoordinateDomain (ι := ι) := by
    rw [liftedConeLogSumExpStrictCoordinateDomain]
    refine mem_iInter.2 ?_
    intro i
    rcases hzi : liftedConeLogSumExpCoordinate (ι := ι) i pBar with ⟨⟨x, y⟩, τ⟩
    have hstrict :
        0 < τ ∧ τ * Real.exp (x / τ) < y :=
      (mem_interior_closure_exponentialCone_iff_strict x y τ).1 (by simpa [hzi] using hcoord_int i)
    simpa [hzi] using (mem_interior_exponentialCone_iff_strict x y τ).2 hstrict
  exact hpBar_not_int <|
    (mem_interior_closure_liftedConeLogSumExpRelativeDomain_iff_strict_coordinates
      (ι := ι) pBar).2 hpBar_strict

/-- Helper for Theorem 5.4.7.7: along a sequence in the strict scalar region converging to a
frontier point of `closure exponentialCone`, the scalar exponential-cone barrier tends to
`+∞`. -/
private lemma tendsto_atTop_exponentialConeBarrier_of_tendsto_frontier_closure
    (z : ℕ → interior (closure exponentialCone)) {zBar : ((ℝ × ℝ) × ℝ)}
    (hz : Tendsto (fun k ↦ (z k : ((ℝ × ℝ) × ℝ))) atTop (nhds zBar))
    (hzBar : zBar ∈ frontier (closure exponentialCone)) :
    Tendsto (fun k ↦ exponentialConeBarrier (z k)) atTop atTop := by
  let xSeq : ℕ → ℝ := fun k ↦ (z k).1.1.1
  let ySeq : ℕ → ℝ := fun k ↦ (z k).1.1.2
  let τSeq : ℕ → ℝ := fun k ↦ (z k).1.2
  let slackSeq : ℕ → ℝ := fun k ↦ exponentialConeBarrierSlack (z k)
  have hxSeq : Tendsto xSeq atTop (nhds zBar.1.1) := by
    simpa [xSeq] using (continuous_fst.fst.tendsto zBar).comp hz
  have hySeq : Tendsto ySeq atTop (nhds zBar.1.2) := by
    simpa [ySeq] using (continuous_fst.snd.tendsto zBar).comp hz
  have hτSeq : Tendsto τSeq atTop (nhds zBar.2) := by
    simpa [τSeq] using (continuous_snd.tendsto zBar).comp hz
  have hstrict (k : ℕ) :
      0 < τSeq k ∧ τSeq k * Real.exp (xSeq k / τSeq k) < ySeq k := by
    simpa [xSeq, ySeq, τSeq] using
      (mem_interior_closure_exponentialCone_iff_strict (z k).1.1.1 (z k).1.1.2 (z k).1.2).1
        (z k).2
  have hτ_pos : ∀ k : ℕ, 0 < τSeq k := fun k ↦ (hstrict k).1
  have hy_pos : ∀ k : ℕ, 0 < ySeq k := by
    intro k
    exact lt_trans (mul_pos (hτ_pos k) (Real.exp_pos _)) (hstrict k).2
  have hslack_pos : ∀ k : ℕ, 0 < slackSeq k := by
    intro k
    have hdiv : Real.exp (xSeq k / τSeq k) < ySeq k / τSeq k := by
      exact (lt_div_iff₀ (hτ_pos k)).2 <| by simpa [mul_comm] using (hstrict k).2
    have hratio : xSeq k / τSeq k < Real.log (ySeq k / τSeq k) := by
      exact (Real.lt_log_iff_exp_lt (div_pos (hy_pos k) (hτ_pos k))).2 hdiv
    have hlt : xSeq k < τSeq k * Real.log (ySeq k / τSeq k) := by
      simpa [mul_comm] using (div_lt_iff₀ (hτ_pos k)).1 hratio
    dsimp [slackSeq, exponentialConeBarrierSlack]
    linarith
  have hzBar_mem : zBar ∈ closure exponentialCone := by
    simpa [frontier, closure_closure] using hzBar.1
  have hzBar_not_int : zBar ∉ interior (closure exponentialCone) := by
    simpa [frontier, closure_closure] using hzBar.2
  have hτ_nonneg : 0 ≤ zBar.2 :=
    exponentialCone_tau_nonneg_of_mem_closure hzBar_mem
  rcases eq_or_lt_of_le hτ_nonneg with hτ_zero | hτ_pos_bar
  · -- If `τ → 0+`, the `-log τ` summand drives the barrier to `+∞`.
    have hτ0 : Tendsto τSeq atTop (nhds 0) := by
      simpa [τSeq, hτ_zero] using hτSeq
    have hτWithin : Tendsto τSeq atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [nhdsWithin]
      refine Filter.tendsto_inf.2 ?_
      refine ⟨hτ0, ?_⟩
      exact Filter.tendsto_principal.2 <|
        Filter.Eventually.of_forall hτ_pos
    have hlogτ : Tendsto (fun k ↦ Real.log (τSeq k)) atTop atBot :=
      Real.tendsto_log_nhdsGT_zero.comp hτWithin
    have hactive : Tendsto (fun k ↦ -Real.log (τSeq k)) atTop atTop := by
      refine Filter.tendsto_atTop.2 ?_
      intro b
      filter_upwards [Filter.tendsto_atBot.1 hlogτ (-b)] with k hk
      linarith
    let By : ℝ := |zBar.1.2| + 1
    let Bx : ℝ := |zBar.1.1| + 1
    let Bs : ℝ := By + Bx
    have hBy_pos : 0 < By := by
      dsimp [By]
      positivity
    have hBs_pos : 0 < Bs := by
      dsimp [Bs]
      positivity
    have hy_upper : ∀ᶠ k in atTop, ySeq k < By := by
      have hmem : Set.Iio By ∈ nhds zBar.1.2 := by
        have hlt : zBar.1.2 < By := by
          dsimp [By]
          have hle : zBar.1.2 ≤ |zBar.1.2| := le_abs_self zBar.1.2
          linarith
        exact Iio_mem_nhds hlt
      exact hySeq hmem
    have hx_lower : ∀ᶠ k in atTop, -Bx < xSeq k := by
      have hmem : Set.Ioi (-Bx) ∈ nhds zBar.1.1 := by
        have hlt : -Bx < zBar.1.1 := by
          dsimp [Bx]
          have hle : -|zBar.1.1| ≤ zBar.1.1 := neg_abs_le zBar.1.1
          linarith
        exact Ioi_mem_nhds hlt
      exact hxSeq hmem
    have hdom :
        ∀ᶠ k in atTop,
          (-Real.log Bs - Real.log By) + (-Real.log (τSeq k)) ≤
            exponentialConeBarrier (z k) := by
      filter_upwards [hy_upper, hx_lower] with k hyk hxk
      have hslack_upper : slackSeq k < Bs := by
        have haux :
            τSeq k * Real.log (ySeq k / τSeq k) - xSeq k ≤ ySeq k - xSeq k := by
          have hlog_le :
              Real.log (ySeq k / τSeq k) ≤ ySeq k / τSeq k - 1 :=
            Real.log_le_sub_one_of_pos (div_pos (hy_pos k) (hτ_pos k))
          have hmul :
              τSeq k * Real.log (ySeq k / τSeq k) ≤ ySeq k - τSeq k := by
            have := mul_le_mul_of_nonneg_left hlog_le (hτ_pos k).le
            have hrewrite : τSeq k * (ySeq k / τSeq k - 1) = ySeq k - τSeq k := by
              field_simp [(hτ_pos k).ne']
            simpa [hrewrite] using this
          have hlog_bound : τSeq k * Real.log (ySeq k / τSeq k) ≤ ySeq k := by
            calc
              τSeq k * Real.log (ySeq k / τSeq k) ≤ ySeq k - τSeq k := hmul
              _ ≤ ySeq k := by linarith [hτ_pos k]
          exact sub_le_sub_right hlog_bound (xSeq k)
        have hyx : ySeq k - xSeq k < Bs := by
          dsimp [Bs]
          linarith
        dsimp [slackSeq, exponentialConeBarrierSlack]
        exact lt_of_le_of_lt haux hyx
      have hterm :
          (-Real.log Bs - Real.log By) + (-Real.log (τSeq k)) ≤
            -Real.log (slackSeq k) - Real.log (ySeq k) - Real.log (τSeq k) := by
        have hslog : -Real.log Bs ≤ -Real.log (slackSeq k) := by
          have hs : Real.log (slackSeq k) ≤ Real.log Bs :=
            Real.log_le_log (hslack_pos k) hslack_upper.le
          linarith
        have hylog : -Real.log By ≤ -Real.log (ySeq k) := by
          have hy' : Real.log (ySeq k) ≤ Real.log By :=
            Real.log_le_log (hy_pos k) hyk.le
          linarith
        linarith
      rw [exponentialConeBarrier_apply]
      dsimp [xSeq, ySeq, τSeq, slackSeq, exponentialConeBarrierSlack] at hterm ⊢
      linarith
    have hshift : Tendsto
        (fun k ↦ (-Real.log Bs - Real.log By) + (-Real.log (τSeq k))) atTop atTop := by
      have hadd : Tendsto (fun t : ℝ ↦ (-Real.log Bs - Real.log By) + t) atTop atTop := by
        rw [Filter.Tendsto]
        simpa [Filter.map_map, add_comm, add_left_comm, add_assoc] using
          le_of_eq (Filter.map_add_atTop_eq (-Real.log Bs - Real.log By))
      exact hadd.comp hactive
    exact tendsto_atTop_mono' atTop hdom hshift
  · -- If `τ̄ > 0`, the frontier condition forces the slack to vanish.
    have hyBar : 0 < zBar.1.2 := by
      have hslack_nonneg : 0 ≤ exponentialConeSlack zBar :=
        exponentialConeSlack_nonneg_of_mem_closure hzBar_mem hτ_pos_bar
      have hpos : 0 < zBar.2 * Real.exp (zBar.1.1 / zBar.2) := by
        exact mul_pos hτ_pos_bar (Real.exp_pos _)
      dsimp [exponentialConeSlack] at hslack_nonneg
      linarith
    have hslack_nonneg : 0 ≤ exponentialConeBarrierSlack zBar :=
      exponentialConeBarrierSlack_nonneg_of_mem_closure hzBar_mem hτ_pos_bar
    have hslack_zero : exponentialConeBarrierSlack zBar = 0 := by
      have hnot_pos : ¬ 0 < exponentialConeBarrierSlack zBar := by
        intro hpos
        have hmem :
            zBar ∈ interior (closure exponentialCone) := by
          rcases zBar with ⟨⟨xBar, yBar⟩, τBar⟩
          have hratio : xBar / τBar < Real.log (yBar / τBar) := by
            have hlt : xBar < τBar * Real.log (yBar / τBar) := by
              dsimp [exponentialConeBarrierSlack] at hpos
              linarith
            have hlt' : xBar < Real.log (yBar / τBar) * τBar := by
              simpa [mul_comm] using hlt
            exact (div_lt_iff₀ hτ_pos_bar).2 hlt'
          have hdiv : Real.exp (xBar / τBar) < yBar / τBar := by
            exact (Real.lt_log_iff_exp_lt (div_pos hyBar hτ_pos_bar)).1 hratio
          have hstrict' : τBar * Real.exp (xBar / τBar) < yBar := by
            simpa [mul_comm] using (lt_div_iff₀ hτ_pos_bar).1 hdiv
          exact
            (mem_interior_closure_exponentialCone_iff_strict xBar yBar τBar).2
              ⟨hτ_pos_bar, hstrict'⟩
        exact hzBar_not_int hmem
      exact le_antisymm (le_of_not_gt hnot_pos) hslack_nonneg
    have hslackTendsto : Tendsto slackSeq atTop (nhds 0) := by
      have hcont : ContinuousAt exponentialConeBarrierSlack zBar :=
        continuousAt_exponentialConeBarrierSlack hτ_pos_bar hyBar
      simpa [slackSeq, hslack_zero] using hcont.tendsto.comp hz
    have hslackWithin : Tendsto slackSeq atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [nhdsWithin]
      refine Filter.tendsto_inf.2 ?_
      refine ⟨hslackTendsto, ?_⟩
      exact Filter.tendsto_principal.2 <|
        Filter.Eventually.of_forall hslack_pos
    have hlogslack : Tendsto (fun k ↦ Real.log (slackSeq k)) atTop atBot :=
      Real.tendsto_log_nhdsGT_zero.comp hslackWithin
    have hactive : Tendsto (fun k ↦ -Real.log (slackSeq k)) atTop atTop := by
      refine Filter.tendsto_atTop.2 ?_
      intro b
      filter_upwards [Filter.tendsto_atBot.1 hlogslack (-b)] with k hk
      linarith
    let By : ℝ := |zBar.1.2| + 1
    let Bτ : ℝ := zBar.2 + 1
    have hBy_pos : 0 < By := by
      dsimp [By]
      positivity
    have hBτ_pos : 0 < Bτ := by
      dsimp [Bτ]
      positivity
    have hy_upper : ∀ᶠ k in atTop, ySeq k < By := by
      have hmem : Set.Iio By ∈ nhds zBar.1.2 := by
        have hlt : zBar.1.2 < By := by
          dsimp [By]
          have hle : zBar.1.2 ≤ |zBar.1.2| := le_abs_self zBar.1.2
          linarith
        exact Iio_mem_nhds hlt
      exact hySeq hmem
    have hτ_upper : ∀ᶠ k in atTop, τSeq k < Bτ := by
      have hmem : Set.Iio Bτ ∈ nhds zBar.2 := by
        have hlt : zBar.2 < Bτ := by
          dsimp [Bτ]
          linarith
        exact Iio_mem_nhds hlt
      exact hτSeq hmem
    have hdom :
        ∀ᶠ k in atTop,
          (-Real.log By - Real.log Bτ) + (-Real.log (slackSeq k)) ≤
            exponentialConeBarrier (z k) := by
      filter_upwards [hy_upper, hτ_upper] with k hyk hτk
      have hylog : -Real.log By ≤ -Real.log (ySeq k) := by
        have hy' : Real.log (ySeq k) ≤ Real.log By :=
          Real.log_le_log (hy_pos k) hyk.le
        linarith
      have hτlog : -Real.log Bτ ≤ -Real.log (τSeq k) := by
        have hτ' : Real.log (τSeq k) ≤ Real.log Bτ :=
          Real.log_le_log (hτ_pos k) hτk.le
        linarith
      have hterm :
          (-Real.log By - Real.log Bτ) + (-Real.log (slackSeq k)) ≤
            -Real.log (slackSeq k) - Real.log (ySeq k) - Real.log (τSeq k) := by
        linarith
      simpa [xSeq, ySeq, τSeq, slackSeq, exponentialConeBarrier_apply,
        exponentialConeBarrierSlack] using hterm
    have hshift : Tendsto
        (fun k ↦ (-Real.log By - Real.log Bτ) + (-Real.log (slackSeq k))) atTop atTop := by
      have hadd : Tendsto (fun t : ℝ ↦ (-Real.log By - Real.log Bτ) + t) atTop atTop := by
        rw [Filter.Tendsto]
        simpa [Filter.map_map, add_comm, add_left_comm, add_assoc] using
          le_of_eq (Filter.map_add_atTop_eq (-Real.log By - Real.log Bτ))
      exact hadd.comp hactive
    exact tendsto_atTop_mono' atTop hdom hshift

/-- Helper for Theorem 5.4.7.7: every convergent normalized coordinate sequence contributes an
eventual lower bound for its scalar barrier summand. -/
private lemma exists_eventual_lower_bound_exponentialConeBarrier_coordinate_of_tendsto
    (x : ℕ → interior (closure D)) {pBar : H}
    (hx : Tendsto (fun k ↦ (x k : H)) atTop (nhds pBar)) (j : ι) :
    ∃ c : ℝ,
      ∀ᶠ k in atTop,
        c ≤ exponentialConeBarrier (liftedConeLogSumExpCoordinate (ι := ι) j (x k).1) := by
  let zBar : ((ℝ × ℝ) × ℝ) := liftedConeLogSumExpCoordinate (ι := ι) j pBar
  let xSeq : ℕ → ℝ := fun k ↦ (liftedConeLogSumExpCoordinate (ι := ι) j (x k).1).1.1
  let ySeq : ℕ → ℝ := fun k ↦ (liftedConeLogSumExpCoordinate (ι := ι) j (x k).1).1.2
  let τSeq : ℕ → ℝ := fun k ↦ (liftedConeLogSumExpCoordinate (ι := ι) j (x k).1).2
  let slackSeq : ℕ → ℝ := fun k ↦
    exponentialConeBarrierSlack (liftedConeLogSumExpCoordinate (ι := ι) j (x k).1)
  have hcoord :
      Tendsto (fun k ↦ liftedConeLogSumExpCoordinate (ι := ι) j (x k).1) atTop (nhds zBar) := by
    simpa [zBar] using
      ((continuous_liftedConeLogSumExpCoordinate (ι := ι) j).tendsto pBar).comp hx
  have hxSeq : Tendsto xSeq atTop (nhds zBar.1.1) := by
    simpa [xSeq, zBar] using (continuous_fst.fst.tendsto zBar).comp hcoord
  have hySeq : Tendsto ySeq atTop (nhds zBar.1.2) := by
    simpa [ySeq, zBar] using (continuous_fst.snd.tendsto zBar).comp hcoord
  have hτSeq : Tendsto τSeq atTop (nhds zBar.2) := by
    simpa [τSeq, zBar] using (continuous_snd.tendsto zBar).comp hcoord
  have hstrict (k : ℕ) :
      0 < τSeq k ∧ τSeq k * Real.exp (xSeq k / τSeq k) < ySeq k := by
    have hcoord_mem :
        liftedConeLogSumExpCoordinate (ι := ι) j (x k).1 ∈ interior (closure exponentialCone) :=
      liftedConeLogSumExpCoordinate_mem_interior_closure_of_mem_interior_closure
        (ι := ι) (x k).2 j
    simpa [xSeq, ySeq, τSeq] using
      (mem_interior_closure_exponentialCone_iff_strict
        (xSeq k) (ySeq k) (τSeq k)).1 hcoord_mem
  have hτ_pos : ∀ k : ℕ, 0 < τSeq k := fun k ↦ (hstrict k).1
  have hy_pos : ∀ k : ℕ, 0 < ySeq k := by
    intro k
    exact lt_trans (mul_pos (hτ_pos k) (Real.exp_pos _)) (hstrict k).2
  have hslack_pos : ∀ k : ℕ, 0 < slackSeq k := by
    intro k
    have hdiv : Real.exp (xSeq k / τSeq k) < ySeq k / τSeq k := by
      exact (lt_div_iff₀ (hτ_pos k)).2 <| by simpa [mul_comm] using (hstrict k).2
    have hratio : xSeq k / τSeq k < Real.log (ySeq k / τSeq k) := by
      exact (Real.lt_log_iff_exp_lt (div_pos (hy_pos k) (hτ_pos k))).2 hdiv
    have hlt : xSeq k < τSeq k * Real.log (ySeq k / τSeq k) := by
      simpa [mul_comm] using (div_lt_iff₀ (hτ_pos k)).1 hratio
    dsimp [slackSeq, exponentialConeBarrierSlack]
    linarith
  let By : ℝ := |zBar.1.2| + 1
  let Bx : ℝ := |zBar.1.1| + 1
  let Bτ : ℝ := |zBar.2| + 1
  let Bs : ℝ := By + Bx
  have hBy_pos : 0 < By := by
    dsimp [By]
    positivity
  have hBτ_pos : 0 < Bτ := by
    dsimp [Bτ]
    positivity
  have hBs_pos : 0 < Bs := by
    dsimp [Bs]
    positivity
  have hy_upper : ∀ᶠ k in atTop, ySeq k < By := by
    have hmem : Set.Iio By ∈ nhds zBar.1.2 := by
      have hlt : zBar.1.2 < By := by
        dsimp [By]
        have hle : zBar.1.2 ≤ |zBar.1.2| := le_abs_self zBar.1.2
        linarith
      exact Iio_mem_nhds hlt
    exact hySeq hmem
  have hx_lower : ∀ᶠ k in atTop, -Bx < xSeq k := by
    have hmem : Set.Ioi (-Bx) ∈ nhds zBar.1.1 := by
      have hlt : -Bx < zBar.1.1 := by
        dsimp [Bx]
        have hle : -|zBar.1.1| ≤ zBar.1.1 := neg_abs_le zBar.1.1
        linarith
      exact Ioi_mem_nhds hlt
    exact hxSeq hmem
  have hτ_upper : ∀ᶠ k in atTop, τSeq k < Bτ := by
    have hmem : Set.Iio Bτ ∈ nhds zBar.2 := by
      have hlt : zBar.2 < Bτ := by
        dsimp [Bτ]
        have hle : zBar.2 ≤ |zBar.2| := le_abs_self zBar.2
        linarith
      exact Iio_mem_nhds hlt
    exact hτSeq hmem
  refine ⟨-Real.log Bs - Real.log By - Real.log Bτ, ?_⟩
  filter_upwards [hy_upper, hx_lower, hτ_upper] with k hyk hxk hτk
  have hslack_upper : slackSeq k < Bs := by
    have haux :
        τSeq k * Real.log (ySeq k / τSeq k) - xSeq k ≤ ySeq k - xSeq k := by
      have hlog_le :
          Real.log (ySeq k / τSeq k) ≤ ySeq k / τSeq k - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (hy_pos k) (hτ_pos k))
      have hmul :
          τSeq k * Real.log (ySeq k / τSeq k) ≤ ySeq k - τSeq k := by
        have := mul_le_mul_of_nonneg_left hlog_le (hτ_pos k).le
        have hrewrite : τSeq k * (ySeq k / τSeq k - 1) = ySeq k - τSeq k := by
          field_simp [(hτ_pos k).ne']
        simpa [hrewrite] using this
      have hlog_bound : τSeq k * Real.log (ySeq k / τSeq k) ≤ ySeq k := by
        calc
          τSeq k * Real.log (ySeq k / τSeq k) ≤ ySeq k - τSeq k := hmul
          _ ≤ ySeq k := by linarith [hτ_pos k]
      exact sub_le_sub_right hlog_bound (xSeq k)
    have hyx : ySeq k - xSeq k < Bs := by
      dsimp [Bs]
      linarith
    dsimp [slackSeq, exponentialConeBarrierSlack]
    exact lt_of_le_of_lt haux hyx
  have hslog : -Real.log Bs ≤ -Real.log (slackSeq k) := by
    have hs' : Real.log (slackSeq k) ≤ Real.log Bs :=
      Real.log_le_log (hslack_pos k) hslack_upper.le
    linarith
  have hylog : -Real.log By ≤ -Real.log (ySeq k) := by
    have hy' : Real.log (ySeq k) ≤ Real.log By :=
      Real.log_le_log (hy_pos k) hyk.le
    linarith
  have hτlog : -Real.log Bτ ≤ -Real.log (τSeq k) := by
    have hτ' : Real.log (τSeq k) ≤ Real.log Bτ :=
      Real.log_le_log (hτ_pos k) hτk.le
    linarith
  have hterm :
      -Real.log Bs - Real.log By - Real.log Bτ ≤
        -Real.log (slackSeq k) - Real.log (ySeq k) - Real.log (τSeq k) := by
    linarith
  rw [exponentialConeBarrier_apply]
  dsimp [xSeq, ySeq, τSeq, slackSeq, exponentialConeBarrierSlack] at hterm ⊢
  linarith

-- Proof sketch: work in the subtype ambient space cut out by `∑ i, y i = τ`, and take the closed
-- feasible set `closure liftedConeLogSumExpRelativeDomain` so Chapter 1's barrier owner applies
-- in the correct ambient space. Its interior is the relative interior of `hat Q`. The coordinate
-- functions `y i`, `τ`, and
-- `t + τ * log (y i) - x i - τ * log τ = (t - x i) + τ * log (y i / τ)` are positive on the
-- relative interior, making the logarithmic sum continuous there. If a sequence in the relative
-- interior approaches the frontier of the closed normalized region, then either some `y i`, `τ`,
-- or one of the logarithmic slack terms tends to `0`, forcing the corresponding term of `Ψ_L` to
-- diverge to `+∞`.
/-- Theorem 5.4.7.7: restricting `Ψ_L(x, y, t, τ)` to the nesterovHyperplane `∑ i, y^(i) = τ` yields a
barrier function on the closed normalized lifted log-sum-exp region
`closure liftedConeLogSumExpRelativeDomain`, viewed in its intrinsic relative ambient space. -/
theorem liftedConeLogSumExpBarrier_restriction_isBarrierFunctionOn :
    IsBarrierFunctionOn
      (closure D)
      liftedConeLogSumExpRelativeBarrierMap := by
  let _ : Fact (IsClosed (closure D)) := ⟨isClosed_closure⟩
  refine IsBarrierFunctionOn.mk ?_ ?_
  · -- First produce an explicit strict feasible point and push it into the intrinsic interior.
    rcases liftedConeLogSumExpStrictCoordinateDomain_nonempty (ι := ι) with ⟨p, hp⟩
    exact ⟨p, liftedConeLogSumExpStrictCoordinateDomain_subset_interior_closure (ι := ι) hp⟩
  · intro x pBar hx hpBar
    classical
    by_cases hι : IsEmpty ι
    · -- In the empty-index case, the relative domain is all of `H`, so the frontier is empty.
      have hD : D = Set.univ := by
        ext p
        rw [mem_liftedConeLogSumExpRelativeDomain_iff_forall_coordinate]
        simp [isEmpty_iff.mp hι]
      have : False := by
        simpa [hD] using hpBar
      exact False.elim this
    · letI : Nonempty ι := not_isEmpty_iff.mp hι
      obtain ⟨i, hi⟩ :=
        exists_coordinate_mem_frontier_closure_exponentialCone_of_mem_frontier_closure_liftedConeLogSumExpRelativeDomain
          (ι := ι) hpBar
      let activeSeq : ℕ → interior (closure exponentialCone) := fun k ↦
        let hz :
            liftedConeLogSumExpCoordinate (ι := ι) i (x k).1 ∈ interior (closure exponentialCone) :=
          liftedConeLogSumExpCoordinate_mem_interior_closure_of_mem_interior_closure
            (ι := ι) (x k).2 i
        ⟨liftedConeLogSumExpCoordinate (ι := ι) i (x k).1, hz⟩
      have hactiveSeq :
          Tendsto (fun k ↦ (activeSeq k : ((ℝ × ℝ) × ℝ))) atTop
            (nhds (liftedConeLogSumExpCoordinate (ι := ι) i pBar)) := by
        have hcoord :
            Tendsto (fun k ↦ liftedConeLogSumExpCoordinate (ι := ι) i (x k).1) atTop
              (nhds (liftedConeLogSumExpCoordinate (ι := ι) i pBar)) := by
          simpa using
            ((continuous_liftedConeLogSumExpCoordinate (ι := ι) i).tendsto pBar).comp hx
        simpa [activeSeq] using hcoord
      have hactive :
          Tendsto (fun k ↦ exponentialConeBarrier (liftedConeLogSumExpCoordinate (ι := ι) i (x k).1))
            atTop atTop := by
        simpa [activeSeq] using
          tendsto_atTop_exponentialConeBarrier_of_tendsto_frontier_closure
            (z := activeSeq) hactiveSeq hi
      choose c hc using
        fun j : ι ↦
          exists_eventual_lower_bound_exponentialConeBarrier_coordinate_of_tendsto
            (ι := ι) x hx j
      have hsum_lower :
          ∀ᶠ k in atTop,
            Finset.sum (Finset.univ.erase i) c ≤
              Finset.sum (Finset.univ.erase i)
                (fun j ↦ exponentialConeBarrier (liftedConeLogSumExpCoordinate (ι := ι) j (x k).1)) := by
        -- Every inactive coordinate contributes an eventual lower bound.
        filter_upwards
          [(Finset.eventually_all (Finset.univ.erase i)).2
            (fun j hj ↦ hc j)] with k hk
        exact Finset.sum_le_sum (fun j hj ↦ hk j hj)
      let C : ℝ := Finset.sum (Finset.univ.erase i) c
      have hshift :
          Tendsto
            (fun k ↦ C + exponentialConeBarrier (liftedConeLogSumExpCoordinate (ι := ι) i (x k).1))
            atTop atTop := by
        -- Adding the finite inactive lower-bound constant preserves divergence to `+∞`.
        have hadd : Tendsto (fun t : ℝ ↦ C + t) atTop atTop := by
          rw [Filter.Tendsto]
          simpa [Filter.map_map, add_comm, add_left_comm, add_assoc] using
            le_of_eq (Filter.map_add_atTop_eq C)
        exact hadd.comp hactive
      have hdom :
          ∀ᶠ k in atTop,
            C + exponentialConeBarrier (liftedConeLogSumExpCoordinate (ι := ι) i (x k).1) ≤
              liftedConeLogSumExpRelativeBarrierMap (x k) := by
        filter_upwards [hsum_lower] with k hk
        have hleft :
            C + exponentialConeBarrier (liftedConeLogSumExpCoordinate (ι := ι) i (x k).1) ≤
              Finset.sum (Finset.univ.erase i)
                (fun j ↦ exponentialConeBarrier (liftedConeLogSumExpCoordinate (ι := ι) j (x k).1)) +
                exponentialConeBarrier (liftedConeLogSumExpCoordinate (ι := ι) i (x k).1) := by
          have hk' :
              C ≤
                Finset.sum (Finset.univ.erase i)
                  (fun j ↦ exponentialConeBarrier (liftedConeLogSumExpCoordinate (ι := ι) j (x k).1)) := by
            simpa [C] using hk
          linarith
        have hsum_eq :
            Finset.sum (Finset.univ.erase i)
                (fun j ↦ exponentialConeBarrier (liftedConeLogSumExpCoordinate (ι := ι) j (x k).1)) +
              exponentialConeBarrier (liftedConeLogSumExpCoordinate (ι := ι) i (x k).1) =
                liftedConeLogSumExpRelativeBarrierMap (x k) := by
          rw [liftedConeLogSumExpRelativeBarrierMap_apply,
            liftedConeLogSumExpHyperplaneBarrier_eq_sum_coordinates]
          simpa using
            Finset.sum_erase_add
              (Finset.univ : Finset ι)
              (fun j ↦ exponentialConeBarrier (liftedConeLogSumExpCoordinate (ι := ι) j (x k).1))
              (by simp : i ∈ (Finset.univ : Finset ι))
        exact le_trans hleft (le_of_eq hsum_eq)
      exact tendsto_atTop_mono' atTop hdom hshift
