/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_4_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.RealProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_6_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_6_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_3.Prereqs
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Nesterov.Chap05.Theorem_5_4_7_3
open scoped PowerConeGeometricMean

attribute [local instance 10000] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance 10000] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance 10000] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance 10000] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance 10000] Chap05RealProdL2.instCompleteSpaceRealProd
attribute [local instance 10000] Chap05RealProdL2.instSeminormedAddCommGroupRealProdProd
attribute [local instance 10000] Chap05RealProdL2.instNormedAddCommGroupRealProdProd
attribute [local instance 10000] Chap05RealProdL2.instNormedSpaceRealProdProd
attribute [local instance 10000] Chap05RealProdL2.instInnerProductSpaceRealProdProd
attribute [local instance 10000] Chap05RealProdL2.instCompleteSpaceRealProdProd

open scoped PowerCone

/- Theorem 5.4.7.3 is a barrier theorem in the Chapter 5 power-cone domain.

Sampled owner declarations:
* `powerCone` from `Definition_5_4_7_1`, the earlier source-facing owner for `K_α`;
* `coneCompositionBarrier` from `Definition_5_4_6_5`, the generic owner for the composed barrier
  used here;
* `power_cone_plus_barrier_apply` from `Theorem_5_4_7_4`, the adjacent bridge theorem evaluating
  the one-sided specialization of the same generic owner shape;
* `ξ[α]`, `powerConeBarrier`, and the swapped-coordinate specialization
  `secondOrderConeBarrier ∘ Prod.swap`, the earlier primitive factor data for the same
  cone-composition construction;
* `powerConeGeometricMean_isOneCompatibleWith_powerConeBarrier` from `Theorem_5_4_7_2`, the
  compatibility theorem feeding the proof route.

Source/core/bridge triage:
* source-facing: the barrier owner `power_cone_barrier α` and the resulting four-self-concordant
  barrier statement on `powerCone α`;
* core/canonical: the earlier owner `coneCompositionBarrier` specialized to the power-cone data;
* bridge/view: the explicit logarithmic evaluation formula below.

Primitive data:
* `powerConeBarrier`;
* `secondOrderConeBarrier ∘ Prod.swap`;
* `ξ[α]`;
* the source-facing cone owner `powerCone α`.

Derived API:
* the source-facing barrier owner `power_cone_barrier α`;
* the pointwise evaluation formula below;
* the resulting `4`-self-concordant barrier statement on `interior (powerCone α)`.

This refinement keeps `coneCompositionBarrier` as the core owner abstraction for the proof route,
but exposes the textbook power-cone barrier itself through the shorter source-facing owner
`power_cone_barrier α`, matching the adjacent chapter API. -/

/-- The logarithmic barrier `Ψ_P` for the symmetric power cone `K_α`, presented as the
source-facing specialization of the chapter's canonical cone-composition barrier owner. -/
def power_cone_barrier (α : ℝ) : ((ℝ × ℝ) × ℝ) → ℝ :=
  coneCompositionBarrier
    powerConeBarrier
    (secondOrderConeBarrier ∘ Prod.swap)
    ξ[α]
    1

-- Proof sketch: on the nonnegative orthant, evaluate `power_cone_barrier α` at
-- `((x₁, x₂), z)` using the upstream pointwise formulas for `secondOrderConeBarrier ∘ Prod.swap`,
-- `powerConeBarrier`, and `ξ[α]`, then rewrite the square
-- `(x₁^α x₂^(1 - α))^2` as `x₁^(2 α) x₂^(2 (1 - α))`.
/-- Evaluating `power_cone_barrier α` at `((x₁, x₂), z)` on the nonnegative orthant
reproduces the textbook formula
`-log ((x₁)^(2 α) (x₂)^(2 (1 - α)) - z^2) - log x₁ - log x₂`. -/
theorem power_cone_barrier_apply
    (α x₁ x₂ z : ℝ) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) :
    power_cone_barrier α ((x₁, x₂), z) =
      -Real.log
          (Real.rpow x₁ (2 * α) * Real.rpow x₂ (2 * (1 - α)) - z ^ (2 : ℕ)) -
        Real.log x₁ - Real.log x₂ := by
  rw [power_cone_barrier, coneCompositionBarrier_apply, secondOrderConeBarrier_swap_apply,
    powerConeBarrier_apply, powerConeGeometricMean_apply]
  norm_num
  have hx₁_square : Real.rpow x₁ α ^ (2 : ℕ) = Real.rpow x₁ (α * 2) := by
    simpa using (Real.rpow_mul_natCast hx₁ α 2).symm
  have hx₂_square : Real.rpow x₂ (1 - α) ^ (2 : ℕ) = Real.rpow x₂ ((1 - α) * 2) := by
    simpa using (Real.rpow_mul_natCast hx₂ (1 - α) 2).symm
  have hsquare :
      (Real.rpow x₁ α * Real.rpow x₂ (1 - α)) ^ (2 : ℕ) =
        Real.rpow x₁ (2 * α) * Real.rpow x₂ (2 * (1 - α)) := by
    calc
      (Real.rpow x₁ α * Real.rpow x₂ (1 - α)) ^ (2 : ℕ) =
          (Real.rpow x₁ α) ^ (2 : ℕ) * (Real.rpow x₂ (1 - α)) ^ (2 : ℕ) := by
            ring
      _ = Real.rpow x₁ (α * 2) * Real.rpow x₂ ((1 - α) * 2) := by
        rw [hx₁_square, hx₂_square]
      _ = Real.rpow x₁ (2 * α) * Real.rpow x₂ (2 * (1 - α)) := by
        congr 1 <;> ring_nf
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    congrArg
      (fun t : ℝ ↦ -Real.log (t - z ^ (2 : ℕ)) + (-Real.log x₁ - Real.log x₂))
      hsquare

/-- Helper for Theorem 5.4.7.3: the weighted geometric mean is the concave `C³` map required by
the cone-composition theorem on the orthant `powerConeQ1` in the chapter's `RealProdL2`
ambient. -/
lemma power_cone_geometric_mean_is_three_times_cont_diff_concave_on_with
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    @IsThreeTimesContDiffConcaveOnWith
      (ℝ × ℝ)
      ℝ
      Chap05RealProdL2.instNormedAddCommGroupRealProd
      Chap05RealProdL2.instNormedSpaceRealProd
      Real.normedAddCommGroup
      RCLike.toInnerProductSpaceReal.toNormedSpace
      powerConeQ1
      (ConvexCone.positive ℝ ℝ)
      (powerConeGeometricMean α) := by
  -- Reuse the theorem-local prerequisite module so this file does not recheck the full
  -- concavity proof.
  simpa using
    Prereqs.power_cone_geometric_mean_is_three_times_cont_diff_concave_on_with
      hα₀ hα₁


/-- Helper for Theorem 5.4.7.3: self-concordance on an open domain only depends on the function
values on that domain. -/
private theorem selfConcordantOnWith_congrEqOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {dom : Set E} {Mf : NNReal} {F G : E → ℝ}
    (h : IsSelfConcordantOnWith dom Mf F) (hEq : Set.EqOn F G dom) :
    IsSelfConcordantOnWith dom Mf G := by
  refine
    { isOpen_domain := h.isOpen_domain
      contDiffOn := (contDiffOn_congr fun x hx ↦ (hEq hx).symm).2 h.contDiffOn
      convexOn := h.convexOn.congr hEq
      third_deriv_bound := ?_ }
  intro x hx u
  have hEqAt : G =ᶠ[nhds x] F := by
    refine Filter.mem_of_superset (h.isOpen_domain.mem_nhds hx) ?_
    intro y hy
    exact (hEq hy).symm
  have hFcontAt : ContDiffAt ℝ 3 F x :=
    h.contDiffOn.contDiffAt (h.isOpen_domain.mem_nhds hx)
  have hGcontAt : ContDiffAt ℝ 3 G x :=
    hFcontAt.congr_of_eventuallyEq hEqAt
  -- Rewrite the cubic derivative and Hessian local norm through neighborhood equality.
  have hthird :
      thirdDirectionalDerivative G x u = thirdDirectionalDerivative F x u := by
    have hiter : iteratedFDeriv ℝ 3 G x = iteratedFDeriv ℝ 3 F x :=
      (Filter.EventuallyEq.iteratedFDeriv ℝ hEqAt 3).eq_of_nhds
    simpa [thirdDirectionalDerivative_eq_iteratedFDeriv hGcontAt,
      thirdDirectionalDerivative_eq_iteratedFDeriv hFcontAt] using
      congrArg (fun A ↦ A fun _ ↦ u) hiter
  have hhess : hessian G x = hessian F x := by
    simpa [hessian] using (hEqAt.gradient.fderiv_eq (𝕜 := ℝ))
  have hnorm : hessianLocalNorm G x u = hessianLocalNorm F x u := by
    simp [hessianLocalNorm_def, hhess]
  calc
    |thirdDirectionalDerivative G x u| = |thirdDirectionalDerivative F x u| := by
      rw [hthird]
    _ ≤ 2 * (Mf : ℝ) * hessianLocalNorm F x u ^ (3 : ℕ) := h.third_deriv_bound hx u
    _ = 2 * (Mf : ℝ) * hessianLocalNorm G x u ^ (3 : ℕ) := by
      rw [hnorm]

/-- Helper for Theorem 5.4.7.3: a self-concordant barrier can be transferred across functions
that agree on the open barrier domain. -/
private theorem barrierCongrEqOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {dom : Set E} {ν : NNReal} {F G : E → ℝ}
    (h : IsSelfConcordantBarrierOnWith dom ν F) (hEq : Set.EqOn F G dom) :
    IsSelfConcordantBarrierOnWith dom ν G := by
  refine
    { toIsStandardSelfConcordantOn := by
        simpa using
          selfConcordantOnWith_congrEqOn h.toIsStandardSelfConcordantOn hEq
      barrier_parameter_bound := ?_ }
  intro x hx u
  have hEqAt : G =ᶠ[nhds x] F := by
    refine Filter.mem_of_superset (h.toIsStandardSelfConcordantOn.isOpen_domain.mem_nhds hx) ?_
    intro y hy
    exact (hEq hy).symm
  -- Route correction: transfer the barrier only after both owner spellings are restricted to the
  -- common open domain where their derivatives agree.
  have hgrad : gradient G x = gradient F x := hEqAt.gradient_eq
  have hhess : hessian G x = hessian F x := by
    simpa [hessian] using (hEqAt.gradient.fderiv_eq (𝕜 := ℝ))
  simpa [hgrad, hhess] using h.barrier_parameter_bound hx u

/-- Helper for Theorem 5.4.7.3: the interior of `powerConeQ2 = {(y, z) | y ≥ |z|}` is the strict
region `y > |z|`. -/
private theorem mem_interior_powerConeQ2_iff (y z : ℝ) :
    (y, z) ∈ interior powerConeQ2 ↔ |z| < y := by
  let swapLinear : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearMap
  have hsurj : Function.Surjective swapLinear :=
    (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).surjective
  have hset :
      powerConeQ2 = swapLinear ⁻¹' (secondOrderCone ℝ : Set (ℝ × ℝ)) := by
    rfl
  have hpre :
      interior (swapLinear ⁻¹' (secondOrderCone ℝ : Set (ℝ × ℝ))) =
        swapLinear ⁻¹' interior (secondOrderCone ℝ : Set (ℝ × ℝ)) := by
    simpa using swapLinear.interior_preimage hsurj (secondOrderCone ℝ : Set (ℝ × ℝ))
  rw [hset, hpre]
  simpa [swapLinear, Real.norm_eq_abs] using
    (mem_interior_secondOrderCone_iff (swapLinear (y, z)))

/-- Helper for Theorem 5.4.7.3: a short owner alias for the raw outer barrier
`(y, z) ↦ -log (y - z) - log (y + z)`. -/
private abbrev powerConeQ2OuterBarrier : (ℝ × ℝ) → ℝ :=
  Nesterov.Chap05.Theorem_5_4_7_3.Prereqs.powerConeQ2OuterBarrier

/-- Helper for Theorem 5.4.7.3: evaluating the raw outer owner reproduces the split logarithmic
formula `-log (y - z) - log (y + z)`. -/
private theorem powerConeQ2OuterBarrier_apply (y z : ℝ) :
    powerConeQ2OuterBarrier (y, z) = -Real.log (y - z) - Real.log (y + z) := by
  -- Rewrite the two pulled-back scalar barriers to the textbook pair of logarithmic slacks.
  simp only [powerConeQ2OuterBarrier,
    Nesterov.Chap05.Theorem_5_4_7_3.Prereqs.powerConeQ2OuterBarrier]
  rw [Pi.add_apply, sublevelLogBarrier_apply, sublevelLogBarrier_apply]
  ring_nf

/-- Helper for Theorem 5.4.7.3: the planar comparison set
`powerConeQ2 = {(y, z) | y ≥ |z|}` is closed. -/
private theorem powerConeQ2_closed : IsClosed (powerConeQ2 : Set (ℝ × ℝ)) := by
  simpa using Nesterov.Chap05.Theorem_5_4_7_3.Prereqs.powerConeQ2_closed

/-- Helper for Theorem 5.4.7.3: the planar comparison set
`powerConeQ2 = {(y, z) | y ≥ |z|}` is convex. -/
private theorem powerConeQ2_convex : Convex ℝ (powerConeQ2 : Set (ℝ × ℝ)) := by
  simpa using Nesterov.Chap05.Theorem_5_4_7_3.Prereqs.powerConeQ2_convex

/-- Helper for Theorem 5.4.7.3: the raw outer owner is a `2`-self-concordant barrier on
`interior powerConeQ2`. -/
private theorem powerConeQ2RawBarrierIsTwoSelfConcordantBarrier :
    @IsSelfConcordantBarrierOnWith
      (ℝ × ℝ)
      Chap05RealProdL2.instNormedAddCommGroupRealProd
      Chap05RealProdL2.instInnerProductSpaceRealProd
      Chap05RealProdL2.instCompleteSpaceRealProd
      (interior powerConeQ2)
      (2 : NNReal)
      powerConeQ2OuterBarrier := by
  -- Reuse the proved raw outer-barrier theorem from the theorem-local prerequisite module.
  simpa using
    Nesterov.Chap05.Theorem_5_4_7_3.Prereqs.powerConeQ2RawBarrierIsTwoSelfConcordantBarrier

/-- Helper for Theorem 5.4.7.3: every positive-cone direction `(s, 0)` is a recession direction
of `powerConeQ2`. -/
lemma powerConeQ2_positive_recession
    {s : ℝ} (hs : s ∈ (ConvexCone.positive ℝ ℝ : Set ℝ))
    {p : ℝ × ℝ} (hp : p ∈ powerConeQ2) (τ : ℝ) (hτ : 0 ≤ τ) :
    p + τ • (s, (0 : ℝ)) ∈ powerConeQ2 := by
  simpa using
    Nesterov.Chap05.Theorem_5_4_7_3.Prereqs.powerConeQ2_positive_recession
      hs hp τ hτ


/-- Helper for Theorem 5.4.7.3: interior points of `K_[α]` have strictly positive orthant
coordinates and strict symmetric slack. -/
private theorem strict_of_mem_interior_powerCone
    {α x₁ x₂ z : ℝ} (hx : ((x₁, x₂), z) ∈ interior K_[α]) :
    0 < x₁ ∧ 0 < x₂ ∧ |z| < powerConeGeometricMean α (x₁, x₂) := by
  have hsubset :
      K_[α] ⊆ (Prod.fst : ((ℝ × ℝ) × ℝ) → ℝ × ℝ) ⁻¹' powerConeQ1 := by
    intro p hp
    rcases p with ⟨⟨u, v⟩, w⟩
    have hpCone := (mem_powerCone_iff α u v w).1 hp
    exact (mem_powerConeQ1_iff u v).2 ⟨hpCone.1, hpCone.2.1⟩
  have hx_preimage :
      ((x₁, x₂), z) ∈ interior ((Prod.fst : ((ℝ × ℝ) × ℝ) → ℝ × ℝ) ⁻¹' powerConeQ1) :=
    interior_mono hsubset hx
  have hx_intQ1 : (x₁, x₂) ∈ interior powerConeQ1 := by
    change
      ((x₁, x₂), z) ∈
        (Prod.fst : ((ℝ × ℝ) × ℝ) → ℝ × ℝ) ⁻¹' interior powerConeQ1
    rw [←
      isOpenMap_fst.preimage_interior_eq_interior_preimage
        continuous_fst
        powerConeQ1] at hx_preimage
    exact hx_preimage
  have hcone : ((x₁, x₂), z) ∈ K_[α] := interior_subset hx
  have hmem := (mem_powerCone_iff α x₁ x₂ z).1 hcone
  have hx₁_pos : 0 < x₁ := (mem_interior_powerConeQ1_iff x₁ x₂).1 hx_intQ1 |>.1
  have hx₂_pos : 0 < x₂ := (mem_interior_powerConeQ1_iff x₁ x₂).1 hx_intQ1 |>.2
  have hz_strict : |z| < powerConeGeometricMean α (x₁, x₂) := by
    by_contra hz_not
    have hz_eq : |z| = powerConeGeometricMean α (x₁, x₂) :=
      le_antisymm hmem.2.2 (le_of_not_gt hz_not)
    let γ : ℝ → ((ℝ × ℝ) × ℝ) := fun s ↦ ((x₁, x₂), s)
    have hpre :
        γ ⁻¹' interior K_[α] ∈ nhds z := by
      exact (show Continuous γ by fun_prop).continuousAt.preimage_mem_nhds <|
        IsOpen.mem_nhds isOpen_interior (by simpa [γ] using hx)
    rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hεsub⟩
    by_cases hz_nonneg : 0 ≤ z
    · have hup : z + ε / 2 ∈ Metric.ball z ε := by
        have hhalf_nonneg : 0 ≤ z + ε / 2 - z := by linarith
        rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg hhalf_nonneg]
        linarith
      have hbad : γ (z + ε / 2) ∈ K_[α] := interior_subset (hεsub hup)
      have hbad_mem := (mem_powerCone_iff α x₁ x₂ (z + ε / 2)).1 hbad
      have habs_shift : |z + ε / 2| = |z| + ε / 2 := by
        rw [abs_of_nonneg (by linarith), abs_of_nonneg hz_nonneg]
      rw [habs_shift, hz_eq] at hbad_mem
      linarith
    · have hz_neg : z < 0 := lt_of_not_ge hz_nonneg
      have hdown : z - ε / 2 ∈ Metric.ball z ε := by
        have hdist : |(z - ε / 2 : ℝ) - z| = ε / 2 := by
          have hneg : z - ε / 2 - z = -(ε / 2) := by ring
          have hhalf_neg : -(ε / 2 : ℝ) < 0 := by
            have hhalf_pos : 0 < (ε / 2 : ℝ) := by positivity
            linarith
          rw [hneg, abs_of_neg hhalf_neg]
          ring_nf
        rw [Metric.mem_ball, Real.dist_eq, hdist]
        linarith
      have hbad : γ (z - ε / 2) ∈ K_[α] := interior_subset (hεsub hdown)
      have hbad_mem := (mem_powerCone_iff α x₁ x₂ (z - ε / 2)).1 hbad
      have habs_shift : |z - ε / 2| = |z| + ε / 2 := by
        rw [abs_of_neg (by linarith), abs_of_neg hz_neg]
        ring
      rw [habs_shift, hz_eq] at hbad_mem
      linarith
  -- Route correction: derive strict slack directly from interior membership in `K_[α]`, so the
  -- raw-vs-swapped outer-barrier comparison only happens on the open `Q₂` domain.
  exact ⟨hx₁_pos, hx₂_pos, hz_strict⟩

/-- Helper for Theorem 5.4.7.3: the graph point `((ξ[α] x), z)` of an interior power-cone point
lies in the interior of `powerConeQ2`. -/
private theorem graphPoint_mem_interior_powerConeQ2_of_mem_interior_powerCone
    {α : ℝ} {p : ((ℝ × ℝ) × ℝ)}
    (hp : p ∈ interior K_[α]) :
    ((powerConeGeometricMean α) p.1, p.2) ∈ interior powerConeQ2 := by
  rcases p with ⟨⟨x₁, x₂⟩, z⟩
  have hstrict := strict_of_mem_interior_powerCone hp
  rw [mem_interior_powerConeQ2_iff]
  simpa using hstrict.2.2

/-- Helper for Theorem 5.4.7.3: the raw outer owner agrees with the swapped second-order-cone
barrier on `interior powerConeQ2`. -/
private theorem powerConeQ2OuterBarrier_eq_secondOrderConeBarrierSwapOnInterior :
    Set.EqOn powerConeQ2OuterBarrier (secondOrderConeBarrier ∘ Prod.swap) (interior powerConeQ2) :=
    by
  intro yz hyz
  rcases yz with ⟨y, z⟩
  have hstrict : |z| < y := (mem_interior_powerConeQ2_iff y z).1 hyz
  have hminus : 0 < y - z := by
    linarith [(abs_lt.mp hstrict).2]
  have hplus : 0 < y + z := by
    linarith [(abs_lt.mp hstrict).1]
  calc
    powerConeQ2OuterBarrier (y, z) = -Real.log (y - z) - Real.log (y + z) := by
      exact powerConeQ2OuterBarrier_apply y z
    _ = -(Real.log (y - z) + Real.log (y + z)) := by ring
    _ = -Real.log ((y - z) * (y + z)) := by
      rw [Real.log_mul hminus.ne' hplus.ne']
    _ = (secondOrderConeBarrier ∘ Prod.swap) (y, z) := by
      rw [secondOrderConeBarrier_swap_apply]
      congr 1
      ring

/-- Helper for Theorem 5.4.7.3: the cone-composition barrier built from the raw outer owner
agrees with the source-facing owner on the interior feasible set. -/
private theorem powerConeRawBarrier_eqOn_sourceBarrier (α : ℝ) :
    Set.EqOn
      (coneCompositionBarrier
        powerConeBarrier
        powerConeQ2OuterBarrier
        (powerConeGeometricMean α)
        1)
      (coneCompositionBarrier
        powerConeBarrier
        (secondOrderConeBarrier ∘ Prod.swap)
        (powerConeGeometricMean α)
        1)
      (interior
        (coneCompositionFeasibleSet
          powerConeQ1
          (ConvexCone.positive ℝ ℝ)
          (powerConeGeometricMean α)
          powerConeQ2)) := by
  intro p hp
  have hpPowerCone : p ∈ interior K_[α] := by
    simpa [coneCompositionFeasibleSet_eq_powerCone α] using hp
  have hgraph :
      ((powerConeGeometricMean α) p.1, p.2) ∈ interior powerConeQ2 :=
    graphPoint_mem_interior_powerConeQ2_of_mem_interior_powerCone hpPowerCone
  rcases p with ⟨x, z⟩
  rw [coneCompositionBarrier_apply, coneCompositionBarrier_apply]
  congr 1
  exact powerConeQ2OuterBarrier_eq_secondOrderConeBarrierSwapOnInterior hgraph

/-- Helper for Theorem 5.4.7.3: restate the orthant logarithmic barrier in the chapter
`RealProdL2` pair ambient consumed by the generic cone-composition theorem. -/
private theorem powerConeBarrierIsTwoSelfConcordantBarrierL2 :
    @IsSelfConcordantBarrierOnWith
      (ℝ × ℝ)
      Chap05RealProdL2.instNormedAddCommGroupRealProd
      Chap05RealProdL2.instInnerProductSpaceRealProd
      Chap05RealProdL2.instCompleteSpaceRealProd
      (interior powerConeQ1)
      (2 : NNReal)
      powerConeBarrier := by
  -- The orthant barrier theorem already has the right mathematics; this wrapper only pins the
  -- pair ambient expected by the cone-composition specialization.
  simpa using power_cone_barrier_is_two_self_concordant_barrier

/-- Helper for Theorem 5.4.7.3: restate the `β = 1` compatibility witness in the chapter
`RealProdL2` pair ambient consumed by the generic cone-composition theorem. -/
private theorem powerConeGeometricMeanIsOneCompatibleWithPowerConeBarrierL2
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    @IsBetaCompatibleWith
      (ℝ × ℝ)
      ℝ
      Chap05RealProdL2.instNormedAddCommGroupRealProd
      Chap05RealProdL2.instInnerProductSpaceRealProd
      Chap05RealProdL2.instCompleteSpaceRealProd
      Real.normedAddCommGroup
      RCLike.toInnerProductSpaceReal.toNormedSpace
      powerConeQ1
      (ConvexCone.positive ℝ ℝ)
      powerConeBarrier
      (1 : NNReal)
      (powerConeGeometricMean α) := by
  -- The prerequisite compatibility theorem is already correct; this wrapper only normalizes the
  -- ambient owner spelling before the final specialization call.
  simpa using powerConeGeometricMean_isOneCompatibleWith_powerConeBarrier hα₀ hα₁

/-- Helper for Theorem 5.4.7.3: the generic cone-composition barrier theorem specializes directly
to the local raw power-cone outer owner. -/
private theorem powerConeRawBarrierSpecializationPrereqs
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    IsSelfConcordantBarrierOnWith
      (interior
        (coneCompositionFeasibleSet
          powerConeQ1
          (ConvexCone.positive ℝ ℝ)
          (powerConeGeometricMean α)
          powerConeQ2))
      ((2 : NNReal) + (1 : NNReal) ^ 3 * (2 : NNReal))
      (coneCompositionBarrier
        powerConeBarrier
        powerConeQ2OuterBarrier
        (powerConeGeometricMean α)
        1) := by
  have hF :
      IsSelfConcordantBarrierOnWith
        (interior powerConeQ1)
        (2 : NNReal)
        powerConeBarrier :=
    powerConeBarrierIsTwoSelfConcordantBarrierL2
  have hΦ :
      IsSelfConcordantBarrierOnWith
        (interior powerConeQ2)
        (2 : NNReal)
        powerConeQ2OuterBarrier :=
    powerConeQ2RawBarrierIsTwoSelfConcordantBarrier
  have hbarrier :=
    coneCompositionBarrier_isSelfConcordantBarrierOnWith
      (Q := powerConeQ1)
      (K := ConvexCone.positive ℝ ℝ)
      (Q₂ := powerConeQ2)
      (F := powerConeBarrier)
      (Φ := powerConeQ2OuterBarrier)
      (ξ := powerConeGeometricMean α)
      (β := (1 : NNReal))
      (ν := (2 : NNReal))
      (μ := (2 : NNReal))
      (power_cone_geometric_mean_is_three_times_cont_diff_concave_on_with hα₀ hα₁)
      (powerConeGeometricMeanIsOneCompatibleWithPowerConeBarrierL2 hα₀ hα₁)
      powerConeQ2_closed
      powerConeQ2_convex
      hF
      hΦ
      (fun {s} hs {p} hp τ hτ ↦ powerConeQ2_positive_recession hs hp τ hτ)
  exact hbarrier

/-- Helper for Theorem 5.4.7.3: the canonical raw specialization rewrites to the local raw outer
owner alias used by the source-facing target file. -/
private theorem powerConeRawBarrierSpecialization
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    IsSelfConcordantBarrierOnWith
      (interior
        (coneCompositionFeasibleSet
          powerConeQ1
          (ConvexCone.positive ℝ ℝ)
          (powerConeGeometricMean α)
          powerConeQ2))
      ((2 : NNReal) + (1 : NNReal) ^ 3 * (2 : NNReal))
      (coneCompositionBarrier
        powerConeBarrier
        powerConeQ2OuterBarrier
        (powerConeGeometricMean α)
        1) := by
  exact powerConeRawBarrierSpecializationPrereqs (α := α) hα₀ hα₁

/-- Helper for Theorem 5.4.7.3: the stable raw specialization transfers to the source-facing
swapped second-order-cone owner on the same open feasible domain. -/
private theorem powerConeSourceBarrierSpecialization
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    IsSelfConcordantBarrierOnWith
      (interior
        (coneCompositionFeasibleSet
          powerConeQ1
          (ConvexCone.positive ℝ ℝ)
          (powerConeGeometricMean α)
          powerConeQ2))
      ((2 : NNReal) + (1 : NNReal) ^ 3 * (2 : NNReal))
      (coneCompositionBarrier
        powerConeBarrier
        (secondOrderConeBarrier ∘ Prod.swap)
        (powerConeGeometricMean α)
        1) := by
  have hraw := powerConeRawBarrierSpecialization (α := α) hα₀ hα₁
  -- Transfer the imported raw specialization across the open-domain equality of the two
  -- outer barrier owners.
  exact barrierCongrEqOn hraw (powerConeRawBarrier_eqOn_sourceBarrier α)

/-- Helper for Theorem 5.4.7.3: the generic cone-composition barrier theorem specializes to the
power-cone data with parameter `2 + 1^3 * 2`. -/
lemma powerConeGenericBarrierSpecialization
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    IsSelfConcordantBarrierOnWith
      (interior
        (coneCompositionFeasibleSet
          powerConeQ1
          (ConvexCone.positive ℝ ℝ)
          (powerConeGeometricMean α)
          powerConeQ2))
      ((2 : NNReal) + (1 : NNReal) ^ 3 * (2 : NNReal))
      (coneCompositionBarrier
        powerConeBarrier
        (secondOrderConeBarrier ∘ Prod.swap)
        (powerConeGeometricMean α)
        1) := by
  -- Keep the source-facing specialization as the primary theorem and use the raw theorem only as
  -- a downstream adapter when the split-log owner is needed explicitly.
  exact powerConeSourceBarrierSpecialization hα₀ hα₁

/-- Helper for Theorem 5.4.7.3: the generic feasible-set interior is exactly the source-facing
power-cone interior. -/
private theorem interior_coneCompositionFeasibleSet_eq_interior_powerCone (α : ℝ) :
    interior
      (coneCompositionFeasibleSet
        powerConeQ1
        (ConvexCone.positive ℝ ℝ)
        (powerConeGeometricMean α)
        powerConeQ2) =
      interior K_[α] := by
  -- Rewrite the generic feasible-set owner once so later barrier theorems can stay on
  -- `interior K_[α]`.
  simp [coneCompositionFeasibleSet_eq_powerCone α]

/-- Helper for Theorem 5.4.7.3: the source-facing barrier owner is exactly the generic
cone-composition barrier specialization. -/
lemma powerConeBarrier_eq_coneCompositionBarrier
    (α : ℝ) :
    power_cone_barrier α =
      coneCompositionBarrier
        powerConeBarrier
        (secondOrderConeBarrier ∘ Prod.swap)
        (powerConeGeometricMean α)
        1 := by
  -- This is the definitional owner bridge used by the final rewrite.
  rfl

/-- Helper for Theorem 5.4.7.3: the cone-composition parameter `μ + β^3 ν` specializes to `4`
for `μ = ν = 2` and `β = 1`. -/
private theorem powerConeConeCompositionParameter_eq_four :
    (2 : NNReal) + 2 = 4 := by
  -- Match the normalized parameter shape that survives after the generic specialization.
  norm_num

/-- Helper for Theorem 5.4.7.3: the raw cone-composition parameter
`2 + 1^3 * 2` already normalizes to `4`. -/
private theorem powerConeConeCompositionRawParameter_eq_four :
    ((2 : NNReal) + (1 : NNReal) ^ 3 * (2 : NNReal)) = 4 := by
  -- Normalize the exact parameter expression emitted by the generic specialization.
  norm_num

-- Proof sketch: apply the cone-composition barrier construction with
-- `Q₁ = ℝ_+²`, `F(x₁, x₂) = -log x₁ - log x₂`, `β = 1`, `ξ(x₁, x₂) = x₁^α x₂^(1 - α)`, and
-- `Φ(y, z) = -log (y^2 - z^2)`. Theorem 5.4.7.2 supplies the `1`-compatibility of `ξ` with
-- `F`, and the planar barrier `Φ` has parameter `μ = 2`; together with `ν = 2` for `F`, the
-- composed barrier has parameter `μ + ν = 4` and specializes to the owner barrier below on the
-- interior of `powerCone α`.
/-- Theorem 5.4.7.3: for `0 < α < 1`, the function
`Ψ_P((x₁, x₂), z) = -log ((x₁)^(2 α) (x₂)^(2 (1 - α)) - z^2) - log x₁ - log x₂`
is a `4`-self-concordant barrier for the power cone `K_α`. -/
theorem power_cone_barrier_is_four_self_concordant_barrier
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    IsSelfConcordantBarrierOnWith
      (interior K_[α])
      (4 : NNReal)
      (power_cone_barrier α) := by
  have hbarrier := powerConeGenericBarrierSpecialization hα₀ hα₁
  -- Route correction: the source-facing specialization already matches the final owner, so the
  -- endgame only rewrites the feasible-set interior and normalizes the barrier parameter.
  -- Rewrite the generic feasible-set and barrier owners back to the source-facing theorem.
  rw [← interior_coneCompositionFeasibleSet_eq_interior_powerCone α,
    powerConeBarrier_eq_coneCompositionBarrier α]
  simpa [powerConeConeCompositionRawParameter_eq_four, powerConeConeCompositionParameter_eq_four]
    using hbarrier
