/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Algorithm_6_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_53
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_55
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_59
-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Gradient TotalVariationNotation WeightSequenceNotation WithTopConvexAnalysis

universe u

namespace ConditionalGradientContraction

section HolderGradient

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `HolderGradientOn v Gv Q f g` records that the chosen dual field `g` represents the
within-set derivative of `f` on `Q` at every feasible point and is `v`-Hölder there with
constant `Gv`, using mathlib's canonical on-set Hölder owner `HolderOnWith`. -/
class HolderGradientOn
    (v Gv : NNReal) (Q : Set E) (f : E → ℝ) (g : E → StrongDual ℝ E) : Prop where
  hasFDerivWithinAt {x : E} (hx : x ∈ Q) : HasFDerivWithinAt f (g x) Q x
  holderOn : HolderOnWith Gv v g Q

namespace HolderGradientOn

theorem norm_sub_le
    {v Gv : NNReal} {Q : Set E} {f : E → ℝ} {g : E → StrongDual ℝ E}
    (hf : HolderGradientOn v Gv Q f g) {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    ‖g x - g y‖ ≤ (Gv : ℝ) * Real.rpow ‖x - y‖ (v : ℝ) := by
  simpa [dist_eq_norm] using hf.holderOn.dist_le hx hy

end HolderGradientOn

end HolderGradient

section LinearizedCompositeGap

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The extended-valued feasible-point bridge for the Chapter 6 linearized composite gap,
expressed directly as the concrete `EReal` supremum of the affine-composite gap over `S`.
This keeps the owner on the stable source-facing surface and avoids repeated `WithTop` transport
in the later decrease estimates. -/
abbrev linearizedCompositeGap
    (S : Set E) (Ψ : E → ℝ) (g : StrongDual ℝ E) (x0 : S) : EReal :=
  sSup ((fun x : E ↦ ((g (x0 - x) + Ψ x0 - Ψ x : ℝ) : EReal)) '' S)

end LinearizedCompositeGap

section TotalVariationBridge

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Helper for Theorem 6.14: a finite affine gap does not change when first viewed in
`WithTop ℝ` and then transported to `EReal`. -/
private lemma withTopToEReal_coe_affineGap
    (s : StrongDual ℝ E) (Ψ : E → ℝ) (x0 x : E) :
    withTopToEReal (((s (x0 - x) + Ψ x0 - Ψ x : ℝ) : WithTop ℝ)) =
      ((s (x0 - x) + Ψ x0 - Ψ x : ℝ) : EReal) := by
  -- The affine gap is already finite, so both extended-real views are definitionally identical.
  rfl

/-- Helper for Theorem 6.14: `linearizedCompositeGap S Ψ g x₀` is exactly the concrete
`EReal` supremum of the affine-composite gap over `S`. -/
private lemma linearizedCompositeGap_eq_sSup_image
    (S : Set E) (Ψ : E → ℝ) (g : StrongDual ℝ E) (x0 : S) :
    linearizedCompositeGap S Ψ g x0 =
      sSup ((fun x : E ↦ ((g (x0 - x) + Ψ x0 - Ψ x : ℝ) : EReal)) '' S) := by
  -- Route correction: the direct `EReal` owner is already this explicit supremum, so the
  -- normalization bridge is definitionally stable.
  rfl

/-- In the ambient-gradient specialization, the chosen-dual gap
`linearizedCompositeGap S Ψ g x₀` reduces to the Chapter 6 total-variation owner
`δ[S, f, Ψ](x₀)`. -/
theorem linearModelTotalVariation_eq_linearizedCompositeGap
    (S : Set E) (f Ψ : E → ℝ) (x0 : S) :
    δ[S, f, Ψ](x0) =
      linearizedCompositeGap S Ψ (InnerProductSpace.toDualMap ℝ E (∇ f x0)) x0 := by
  -- Unfold both owner surfaces to the same concrete affine-gap supremum on `S`.
  rw [linearModelTotalVariation_def, linearizedCompositeGap_eq_sSup_image]
  simp [InnerProductSpace.toDualMap_apply_apply]

end TotalVariationBridge

section ContractionErrorTerm

/-- The error quantity `C_{v,t}` attached to the scalar initial gap `Δ(x₀)`, the weights `a_t`,
the canonical accumulated weights `A_t = A[a](t)`, and the Hölder data `G_v` and `D`. This is
the source-facing specialization of `linearOptimizationOracleErrorBound`, with the factor
`(1 + v)⁻¹` absorbed into the Hölder constant. -/
abbrev contractionErrorTerm
    (Δ0 : ℝ) (a : ℕ → ℝ) (Gv D v : ℝ) (t : ℕ) : ℝ :=
  linearOptimizationOracleErrorBound Δ0 a (Gv / (1 + v)) D v t

namespace ContractionErrorNotation

/- Source-facing Lean notation for the Chapter 6 constant `C_{v,t}` with the ambient data fixed
by the surrounding context. -/
scoped notation:max "C[" Δ0 ", " a ", " Gv ", " D ", " v "](" t:arg ")" =>
  contractionErrorTerm Δ0 a Gv D v t

end ContractionErrorNotation

end ContractionErrorTerm

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The estimating functional sequence `φ_t` generated from the weights `a_t`, the initial model
`\tilde f`, the smooth term `f`, the chosen dual gradient field, the regularizer `Ψ`, and the
iterate sequence `x_t`. -/
def estimatingFunctionalSequence
    (a : ℕ → ℝ) (tildeF : E → ℝ) (f : E → ℝ) (gradF : E → StrongDual ℝ E) (Ψ : E → ℝ)
    (xSeq : ℕ → E) : ℕ → E → ℝ
  | 0 => fun x ↦ a 0 * tildeF x
  | t + 1 => fun x ↦
      estimatingFunctionalSequence a tildeF f gradF Ψ xSeq t x +
        a (t + 1) *
          (f (xSeq t) + gradF (xSeq t) (x - xSeq t) + Ψ x)

namespace EstimatingFunctionNotation

/- Source-facing Lean notation for the Chapter 6 estimating sequence `φ_t(x)` with all ambient
data fixed explicitly. -/
scoped notation:max "φ[" a ", " tildeF ", " f ", " gradF ", " Ψ ", " xSeq "]("
    t:arg ", " x:arg ")" =>
  estimatingFunctionalSequence a tildeF f gradF Ψ xSeq t x

end EstimatingFunctionNotation

namespace ContractedFeasibleSetTrustRegionScheme

variable {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}

/-- The estimating functional sequence `φ_t` attached to a contracted-feasible-set trust-region
scheme and an initial model `\tilde f`. -/
abbrev estimatingFunction
    (method : ContractedFeasibleSetTrustRegionScheme problem x0)
    (a : ℕ → ℝ) (tildeF : E → ℝ) : ℕ → E → ℝ :=
  estimatingFunctionalSequence
    a tildeF problem.smoothPart method.gradient (withTopRealPart problem.nonsmoothPart) method

namespace EstimatingFunctionNotation

/- Source-facing Lean notation for the specialized estimating sequence `φ_t(x)` attached to
Algorithm 6.5. -/
scoped notation:max "φ[" method ", " a ", " tildeF "](" t:arg ", " x:arg ")" =>
  ContractedFeasibleSetTrustRegionScheme.estimatingFunction method a tildeF t x

end EstimatingFunctionNotation

end ContractedFeasibleSetTrustRegionScheme

open ContractedFeasibleSetTrustRegionScheme
open scoped ContractionErrorNotation EstimatingFunctionNotation

namespace HolderGradientOn

/-- Helper for Theorem 6.14: points on the segment between two feasible vectors stay feasible. -/
private lemma lineMap_mem_feasible
    {Q : Set E} (hQ_convex : Convex ℝ Q) {x y : E} (hx : x ∈ Q) (hy : y ∈ Q)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap x y t ∈ Q := by
  -- Convexity keeps the full segment inside the feasible set.
  exact hQ_convex.lineMap_mem hx hy ht

/-- Helper for Theorem 6.14: the exact segment increment equals the frozen linearization plus the
integrated derivative-field remainder. -/
private lemma increment_eq_linearization_add_integral_remainder
    {Q : Set E} {f : E → ℝ} {g : E → StrongDual ℝ E} {v Gv : NNReal}
    (hf : HolderGradientOn v Gv Q f g) (hQ_convex : Convex ℝ Q) (hv : 0 < (v : ℝ))
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    f y =
      f x + g x (y - x) +
        ∫ t : ℝ in 0..1, (g (AffineMap.lineMap x y t) - g x) (y - x) := by
  let seg : ℝ → E := AffineMap.lineMap x y
  let remainder : ℝ → ℝ := fun t ↦ (g (seg t) - g x) (y - x)
  let ψ : ℝ → ℝ := fun t ↦ f (seg t) - t * g x (y - x)
  have hseg : Set.MapsTo seg (Set.Icc (0 : ℝ) 1) Q := by
    intro t ht
    exact lineMap_mem_feasible hQ_convex hx hy ht
  have hseg_deriv :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt (fun s ↦ f (seg s)) (g (seg t) (y - x)) (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    -- Compose the within-derivative witness with the segment parameterization.
    simpa [seg] using
      (hf.hasFDerivWithinAt (hseg ht)).comp_hasDerivWithinAt t
        AffineMap.hasDerivWithinAt_lineMap hseg
  have hseg_cont : ContinuousOn (fun t ↦ f (seg t)) (Set.Icc (0 : ℝ) 1) := by
    -- The scalar segment restriction is continuous because it is differentiable on `[0,1]`.
    exact fun t ht ↦ (hseg_deriv t ht).continuousWithinAt
  have hg_cont : ContinuousOn g Q := hf.holderOn.continuousOn hv
  have hremainder_cont : ContinuousOn remainder (Set.Icc (0 : ℝ) 1) := by
    -- Continuity of the derivative field makes the remainder integrand continuous.
    have hgrad_cont : ContinuousOn (fun t ↦ g (seg t)) (Set.Icc (0 : ℝ) 1) :=
      hg_cont.comp AffineMap.lineMap_continuous.continuousOn hseg
    have hsub_cont : ContinuousOn (fun t ↦ g (seg t) - g x) (Set.Icc (0 : ℝ) 1) :=
      hgrad_cont.sub continuousOn_const
    simpa [remainder] using
      hsub_cont.clm_apply
        (show ContinuousOn (fun _ : ℝ ↦ y - x) (Set.Icc (0 : ℝ) 1) from continuousOn_const)
  have hremainder_cont_uIcc : ContinuousOn remainder (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le zero_le_one] using hremainder_cont
  have hremainder_int : IntervalIntegrable remainder MeasureTheory.volume 0 1 :=
    hremainder_cont_uIcc.intervalIntegrable
  have hψ_cont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1) := by
    -- The auxiliary scalar function is continuous on the whole interval.
    have hlin_cont : ContinuousOn (fun t : ℝ ↦ t * g x (y - x)) (Set.Icc (0 : ℝ) 1) :=
      (continuous_id'.mul continuous_const).continuousOn
    simpa [ψ] using hseg_cont.sub hlin_cont
  have hψ_deriv :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivWithinAt ψ (remainder t) (Set.Ioi t) t := by
    intro t ht
    -- Use the right-derivative version of FTC directly on the feasible segment.
    have hseg_deriv_right :
        HasDerivWithinAt (fun s ↦ f (seg s)) (g (seg t) (y - x)) (Set.Ioi t) t :=
      (hseg_deriv t (Set.mem_Icc_of_Ioo ht)).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGT ht.2) (by
          intro s hs
          exact ⟨ht.1.le.trans hs.1, hs.2⟩))
    have hlin_deriv :
        HasDerivWithinAt (fun s : ℝ ↦ s * g x (y - x)) (g x (y - x)) (Set.Ioi t) t := by
      simpa only [one_mul] using ((hasDerivAt_id' t).mul_const (g x (y - x))).hasDerivWithinAt
    simpa [ψ, remainder, sub_eq_add_neg, sub_mul] using hseg_deriv_right.sub hlin_deriv
  have hftc :
      ∫ t : ℝ in 0..1, remainder t = ψ 1 - ψ 0 := by
    -- The one-dimensional FTC gives the exact increment identity.
    exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      zero_le_one hψ_cont hψ_deriv hremainder_int
  have hftc' :
      ∫ t : ℝ in 0..1, remainder t = f y - f x - g x (y - x) := by
    simpa [ψ, remainder, seg, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using hftc
  linarith

/-- Helper for Theorem 6.14: the segment remainder is bounded by the Hölder kernel
`Gᵥ tᵛ ‖y - x‖^(1 + v)`. -/
private lemma segment_remainder_abs_le_holder_kernel
    {Q : Set E} {f : E → ℝ} {g : E → StrongDual ℝ E} {v Gv : NNReal}
    (hf : HolderGradientOn v Gv Q f g) (hQ_convex : Convex ℝ Q)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |((g (AffineMap.lineMap x y t) - g x) (y - x) : ℝ)| ≤
      (Gv : ℝ) * Real.rpow t (v : ℝ) * Real.rpow ‖y - x‖ (1 + (v : ℝ)) := by
  let d : E := y - x
  have ht_nonneg : 0 ≤ t := ht.1
  have hv_nonneg : 0 ≤ (v : ℝ) := by
    exact_mod_cast v.2
  have hline_mem : AffineMap.lineMap x y t ∈ Q :=
    lineMap_mem_feasible hQ_convex hx hy ht
  have hnorm_sub :
      ‖g (AffineMap.lineMap x y t) - g x‖ ≤
        (Gv : ℝ) * Real.rpow ‖AffineMap.lineMap x y t - x‖ (v : ℝ) :=
    hf.norm_sub_le hline_mem hx
  have hdist :
      ‖AffineMap.lineMap x y t - x‖ = t * ‖d‖ := by
    -- Along the segment, distance from `x` scales exactly with `t`.
    calc
      ‖AffineMap.lineMap x y t - x‖ = ‖t • d‖ := by
        simp [d, AffineMap.lineMap_apply_module']
      _ = |t| * ‖d‖ := norm_smul t d
      _ = t * ‖d‖ := by simp [abs_of_nonneg ht_nonneg]
  have hd_rpow :
      Real.rpow ‖d‖ (1 + (v : ℝ)) = Real.rpow ‖d‖ (v : ℝ) * ‖d‖ := by
    simpa [Real.rpow_one, add_comm] using
      (Real.rpow_add_of_nonneg (x := ‖d‖) (y := (v : ℝ)) (z := (1 : ℝ))
        (norm_nonneg d) hv_nonneg zero_le_one)
  -- Bound the scalar remainder by the operator norm of the derivative-field difference.
  calc
    |((g (AffineMap.lineMap x y t) - g x) d : ℝ)| = ‖(g (AffineMap.lineMap x y t) - g x) d‖ := rfl
    _ ≤ ‖g (AffineMap.lineMap x y t) - g x‖ * ‖d‖ :=
      (g (AffineMap.lineMap x y t) - g x).le_opNorm d
    _ ≤ ((Gv : ℝ) * Real.rpow ‖AffineMap.lineMap x y t - x‖ (v : ℝ)) * ‖d‖ := by
      exact mul_le_mul_of_nonneg_right hnorm_sub (norm_nonneg d)
    _ = ((Gv : ℝ) * Real.rpow (t * ‖d‖) (v : ℝ)) * ‖d‖ := by
      rw [hdist]
    _ = ((Gv : ℝ) * (Real.rpow t (v : ℝ) * Real.rpow ‖d‖ (v : ℝ))) * ‖d‖ := by
      congr 2
      simpa using
        (Real.mul_rpow (x := t) (y := ‖d‖) (z := (v : ℝ)) ht_nonneg (norm_nonneg d))
    _ = (Gv : ℝ) * Real.rpow t (v : ℝ) * Real.rpow ‖d‖ (1 + (v : ℝ)) := by
      rw [mul_assoc, mul_assoc, ← hd_rpow]
      ring

/-- Helper for Theorem 6.14: for positive Hölder exponent, the unit-interval integral of `t^v`
is `(1 + v)⁻¹`. -/
private lemma integral_unitInterval_rpow_eq_inv_add
    {v : NNReal} (hv : 0 < (v : ℝ)) :
    ∫ t : ℝ in 0..1, Real.rpow t (v : ℝ) = 1 / (1 + (v : ℝ)) := by
  have hv' : -1 < (v : ℝ) := by linarith
  have hpow_ne : (v : ℝ) + 1 ≠ 0 := by linarith
  -- Evaluate the primitive and simplify the endpoint terms.
  simpa [Real.zero_rpow hpow_ne, add_comm] using
    (integral_rpow (a := (0 : ℝ)) (b := 1) (r := (v : ℝ)) (Or.inl hv'))

/-- Helper for Theorem 6.14: for `v > 0`, a Hölder derivative field gives the sharp first-order
upper model with factor `(1 + v)⁻¹`. -/
private theorem upper_model_pos
    {Q : Set E} {f : E → ℝ} {g : E → StrongDual ℝ E} {v Gv : NNReal}
    (hf : HolderGradientOn v Gv Q f g) (hQ_convex : Convex ℝ Q) (hv : 0 < (v : ℝ))
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    f y ≤
      f x + g x (y - x) +
        ((Gv : ℝ) / (1 + (v : ℝ))) * Real.rpow ‖y - x‖ (1 + (v : ℝ)) := by
  let remainder : ℝ → ℝ := fun t ↦ (g (AffineMap.lineMap x y t) - g x) (y - x)
  let A : ℝ := Real.rpow ‖y - x‖ (1 + (v : ℝ))
  let kernel : ℝ → ℝ := fun t ↦ ((Gv : ℝ) * A) * Real.rpow t (v : ℝ)
  have hincrement :
      f y = f x + g x (y - x) + ∫ t : ℝ in 0..1, remainder t := by
    -- First isolate the exact integral remainder along the feasible segment.
    simpa [remainder] using
      increment_eq_linearization_add_integral_remainder hf hQ_convex hv hx hy
  have hg_cont : ContinuousOn g Q := hf.holderOn.continuousOn hv
  have hseg : Set.MapsTo (AffineMap.lineMap x y) (Set.Icc (0 : ℝ) 1) Q := by
    intro t ht
    exact lineMap_mem_feasible hQ_convex hx hy ht
  have hgrad_cont :
      ContinuousOn (fun t ↦ g (AffineMap.lineMap x y t)) (Set.Icc (0 : ℝ) 1) :=
    hg_cont.comp AffineMap.lineMap_continuous.continuousOn hseg
  have hremainder_cont : ContinuousOn remainder (Set.Icc (0 : ℝ) 1) := by
    -- Continuity of the derivative field turns the remainder into a continuous integrand.
    have hsub_cont :
        ContinuousOn (fun t ↦ g (AffineMap.lineMap x y t) - g x) (Set.Icc (0 : ℝ) 1) :=
      hgrad_cont.sub continuousOn_const
    simpa [remainder] using
      hsub_cont.clm_apply
        (show ContinuousOn (fun _ : ℝ ↦ y - x) (Set.Icc (0 : ℝ) 1) from continuousOn_const)
  have hremainder_cont_uIcc : ContinuousOn remainder (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le zero_le_one] using hremainder_cont
  have hremainder_int : IntervalIntegrable remainder MeasureTheory.volume 0 1 :=
    hremainder_cont_uIcc.intervalIntegrable
  have hkernel_int : IntervalIntegrable kernel MeasureTheory.volume 0 1 := by
    -- The comparison kernel is a constant multiple of `t ↦ t^v`.
    have hrpow_int :
        IntervalIntegrable (fun t : ℝ ↦ Real.rpow t (v : ℝ)) MeasureTheory.volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    simpa [kernel, A, mul_assoc, mul_left_comm, mul_comm] using
      hrpow_int.const_mul ((Gv : ℝ) * A)
  have hpoint :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, remainder t ≤ kernel t := by
    intro t ht
    -- Bound the scalar remainder by its absolute value and then use the Hölder kernel.
    exact le_trans (le_abs_self (remainder t)) <| by
      simpa [remainder, kernel, A, mul_assoc, mul_left_comm, mul_comm] using
        segment_remainder_abs_le_holder_kernel hf hQ_convex hx hy ht
  have hmono :
      ∫ t : ℝ in 0..1, remainder t ≤ ∫ t : ℝ in 0..1, kernel t := by
    exact intervalIntegral.integral_mono_on
      (hf := hremainder_int) (hg := hkernel_int) (hab := zero_le_one) hpoint
  -- Compare the exact increment with the integrated Hölder kernel.
  calc
    f y = f x + g x (y - x) + ∫ t : ℝ in 0..1, remainder t := hincrement
    _ ≤ f x + g x (y - x) + ∫ t : ℝ in 0..1, kernel t := by
      simpa [add_assoc, add_left_comm, add_comm] using
        add_le_add_left hmono (f x + g x (y - x))
    _ = f x + g x (y - x) + ((Gv : ℝ) * A) * (∫ t : ℝ in 0..1, Real.rpow t (v : ℝ)) := by
      simp [kernel, intervalIntegral.integral_const_mul]
    _ = f x + g x (y - x) + ((Gv : ℝ) * A) * (1 / (1 + (v : ℝ))) := by
      rw [integral_unitInterval_rpow_eq_inv_add hv]
    _ = f x + g x (y - x) + ((Gv : ℝ) / (1 + (v : ℝ))) * A := by
      simp [A, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    _ = f x + g x (y - x) + ((Gv : ℝ) / (1 + (v : ℝ))) *
        Real.rpow ‖y - x‖ (1 + (v : ℝ)) := by
      simp [A]

/-- Helper for Theorem 6.14: at the endpoint `v = 0`, the Hölder assumption still yields the
first-order upper model with linear remainder. -/
private theorem upper_model_zero
    {Q : Set E} {f : E → ℝ} {g : E → StrongDual ℝ E} {Gv : NNReal}
    (hf : HolderGradientOn 0 Gv Q f g) (hQ_convex : Convex ℝ Q)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    f y ≤ f x + g x (y - x) + (Gv : ℝ) * ‖y - x‖ := by
  have hnorm :
      ‖f y - f x - g x (y - x)‖ ≤ (Gv : ℝ) * ‖y - x‖ := by
    -- With exponent `0`, every derivative variation is uniformly bounded by `Gᵥ`.
    refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (hf := fun z hz ↦ hf.hasFDerivWithinAt hz)
      (bound := ?_) (hs := hQ_convex) hx hy
    intro z hz
    have hbound := hf.norm_sub_le hz hx
    simpa using hbound
  -- Discard the absolute value to keep the one-sided upper-model estimate.
  have hupper :
      f y - f x - g x (y - x) ≤ (Gv : ℝ) * ‖y - x‖ := by
    exact le_trans (le_abs_self _) hnorm
  linarith

/-- Helper for Theorem 6.14: the first-order upper model is valid uniformly for all
`v : NNReal`, including the endpoint `v = 0`. -/
private theorem upper_model
    {Q : Set E} {f : E → ℝ} {g : E → StrongDual ℝ E} {v Gv : NNReal}
    (hf : HolderGradientOn v Gv Q f g) (hQ_convex : Convex ℝ Q)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    f y ≤
      f x + g x (y - x) +
        ((Gv : ℝ) / (1 + (v : ℝ))) * Real.rpow ‖y - x‖ (1 + (v : ℝ)) := by
  by_cases hv : 0 < (v : ℝ)
  · -- Positive exponents use the sharp integral proof route.
    exact upper_model_pos hf hQ_convex hv hx hy
  · have hv0 : (v : ℝ) = 0 := by
      exact le_antisymm (le_of_not_gt hv) (by exact_mod_cast v.2)
    have hv0' : v = 0 := by
      apply Subtype.ext
      simpa using hv0
    -- The endpoint `v = 0` reduces to the Lipschitz-gradient case.
    subst hv0'
    simpa using upper_model_zero (Gv := Gv) hf hQ_convex hx hy

end HolderGradientOn

/-- Helper for Theorem 6.14: the accumulated weights satisfy `A_{t+1} = A_t + a_{t+1}`. -/
private lemma accumulatedWeights_succ
    (a : ℕ → ℝ) (t : ℕ) :
    accumulatedWeights a (t + 1) = A[a](t) + a (t + 1) := by
  -- Expand the finite sums and isolate the new terminal weight.
  rw [accumulatedWeights_apply, accumulatedWeights_apply, Finset.sum_range_succ]

/-- Helper for Theorem 6.14: positivity of the weights implies positivity of every accumulated
weight `A_t`. -/
private lemma accumulatedWeights_pos
    (a : ℕ → ℝ) (ha_pos : ∀ t : ℕ, 0 < a t) :
    ∀ t : ℕ, 0 < A[a](t) := by
  intro t
  induction t with
  | zero =>
      -- At time `0`, the accumulated weight is exactly `a₀`.
      simpa [accumulatedWeights_apply] using ha_pos 0
  | succ t ih =>
      -- The recursive step adds a positive new weight to the previous positive sum.
      rw [accumulatedWeights_succ]
      linarith [ih, ha_pos (t + 1)]

/-- Helper for Theorem 6.14: the contraction-error term satisfies its defining one-step
recursion. -/
private lemma contractionErrorTerm_succ
    (Δ0 : ℝ) (a : ℕ → ℝ) (Gv D v : ℝ) (t : ℕ) :
    contractionErrorTerm Δ0 a Gv D v (t + 1) =
      contractionErrorTerm Δ0 a Gv D v t +
        (Real.rpow (a (t + 1)) (1 + v) /
          (Real.rpow (accumulatedWeights a (t + 1)) v)) *
          (Gv / (1 + v)) * Real.rpow D (1 + v) := by
  -- Expand the interval sum and peel off the new `k = t + 1` contribution.
  rw [contractionErrorTerm, contractionErrorTerm, linearOptimizationOracleErrorBound_def,
    linearOptimizationOracleErrorBound_def,
    Finset.sum_Icc_succ_top (show 1 ≤ t + 1 by omega)]
  ring

/-- Helper for Theorem 6.14: multiplying the normalized successor inequality by `A_{t+1}`
recovers the affine rescaling `A_{t+1}((1-τ_t)u + τ_t v) = A_t u + a_{t+1} v`. -/
private lemma successor_weighted_average_rescaling
    (a : ℕ → ℝ) (ha_pos : ∀ t : ℕ, 0 < a t)
    (t : ℕ) (u v : ℝ) :
    accumulatedWeights a (t + 1) *
        ((1 - weightCoefficient a t) * u + weightCoefficient a t * v) =
      accumulatedWeights a t * u + a (t + 1) * v := by
  have hA_ne : accumulatedWeights a (t + 1) ≠ 0 :=
    (accumulatedWeights_pos a ha_pos (t + 1)).ne'
  -- Rewrite `τ_t` as `a_{t+1} / A_{t+1}` and clear the unique denominator.
  rw [weightCoefficient_apply]
  field_simp [hA_ne]
  rw [accumulatedWeights_succ]
  ring

/-- Helper for Theorem 6.14: the Hölder remainder written in terms of `τ_t` rescales to the
Chapter 6 increment written with `a_{t+1}` and `A_{t+1}`. -/
private lemma weight_coefficient_holder_rescaling
    (a : ℕ → ℝ) (ha_pos : ∀ t : ℕ, 0 < a t)
    (v Gv D : ℝ) (t : ℕ) :
    accumulatedWeights a (t + 1) *
        (weightCoefficient a t *
          ((Gv / (1 + v)) * Real.rpow D (1 + v) *
            Real.rpow (weightCoefficient a t) v)) =
      (Real.rpow (a (t + 1)) (1 + v) / Real.rpow (accumulatedWeights a (t + 1)) v) *
        (Gv / (1 + v)) * Real.rpow D (1 + v) := by
  have ha_nonneg : 0 ≤ a (t + 1) := (ha_pos (t + 1)).le
  have hA_pos : 0 < accumulatedWeights a (t + 1) := accumulatedWeights_pos a ha_pos (t + 1)
  have hA_nonneg : 0 ≤ accumulatedWeights a (t + 1) := hA_pos.le
  have hA_rpow_ne : Real.rpow (accumulatedWeights a (t + 1)) v ≠ 0 :=
    (Real.rpow_pos_of_pos hA_pos v).ne'
  have hτ_pos : 0 < weightCoefficient a t := by
    rw [weightCoefficient_apply]
    exact div_pos (ha_pos (t + 1)) hA_pos
  have hτ_pow :
      weightCoefficient a t * Real.rpow (weightCoefficient a t) v =
        Real.rpow (weightCoefficient a t) (1 + v) := by
    -- Merge the explicit `τ_t` factor with `τ_t^v`.
    simpa [Real.rpow_one] using (Real.rpow_add hτ_pos 1 v).symm
  have hA_pow :
      Real.rpow (accumulatedWeights a (t + 1)) (1 + v) =
        accumulatedWeights a (t + 1) * Real.rpow (accumulatedWeights a (t + 1)) v := by
    -- Factor the positive power `A_{t+1}^{1+v}` into `A_{t+1} * A_{t+1}^v`.
    simpa [Real.rpow_one, mul_comm, mul_left_comm, mul_assoc] using
      (Real.rpow_add hA_pos 1 v)
  have hdiv :
      Real.rpow (a (t + 1) / accumulatedWeights a (t + 1)) (1 + v) =
        Real.rpow (a (t + 1)) (1 + v) /
          Real.rpow (accumulatedWeights a (t + 1)) (1 + v) := by
    simpa using Real.div_rpow ha_nonneg hA_nonneg (1 + v)
  -- Rewrite the full Hölder increment from the `τ_t`-surface to the `a_{t+1}` / `A_{t+1}` form.
  calc
    accumulatedWeights a (t + 1) *
        (weightCoefficient a t *
          ((Gv / (1 + v)) * Real.rpow D (1 + v) *
            Real.rpow (weightCoefficient a t) v)) =
      accumulatedWeights a (t + 1) *
        (Real.rpow (weightCoefficient a t) (1 + v) *
          ((Gv / (1 + v)) * Real.rpow D (1 + v))) := by
            rw [← hτ_pow]
            ring
    _ =
      accumulatedWeights a (t + 1) *
        ((Real.rpow (a (t + 1)) (1 + v) /
            Real.rpow (accumulatedWeights a (t + 1)) (1 + v)) *
          ((Gv / (1 + v)) * Real.rpow D (1 + v))) := by
            rw [weightCoefficient_apply, hdiv]
    _ =
      accumulatedWeights a (t + 1) *
        ((Real.rpow (a (t + 1)) (1 + v) /
            (accumulatedWeights a (t + 1) * Real.rpow (accumulatedWeights a (t + 1)) v)) *
          ((Gv / (1 + v)) * Real.rpow D (1 + v))) := by
            rw [hA_pow]
    _ =
      (Real.rpow (a (t + 1)) (1 + v) / Real.rpow (accumulatedWeights a (t + 1)) v) *
        (Gv / (1 + v)) * Real.rpow D (1 + v) := by
          field_simp [hA_pos.ne', hA_rpow_ne]

/-- Helper for Theorem 6.14: the successor objective lies within `τ_t D` of the current iterate,
because the contracted feasible set moves by at most the step size. -/
private lemma successor_norm_le_stepSize_mul_diameter
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) {D : ℝ}
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (t : ℕ) :
    ‖method (t + 1) - method t‖ ≤ method.stepSize t * D := by
  let τ := method.stepSize t
  have hτ_nonneg : 0 ≤ τ := (method.stepSize_mem_Ioc t).1.le
  rcases (mem_contractedFeasibleSet_iff.mp
    (method.iterates_succ_mem_and_isMinOn t).1) with ⟨y, hy, hyEq⟩
  -- Rewrite the successor displacement through the contracted-feasible-set witness.
  calc
    ‖method (t + 1) - method t‖ =
      ‖τ • (y - method t)‖ := by
        rw [hyEq]
        dsimp [τ]
        simp [sub_eq_add_neg, smul_add, add_smul, smul_sub, add_assoc, add_left_comm, add_comm]
    _ = τ * ‖y - method t‖ := by
        simpa [Real.norm_of_nonneg hτ_nonneg] using norm_smul τ (y - method t)
    _ ≤ τ * D := by
        exact mul_le_mul_of_nonneg_left (hdiam hy (method.iterates_mem_feasibleSet t)) hτ_nonneg

/-- Helper for Theorem 6.14: the smooth part at the successor iterate is bounded by the frozen
linearization at `x_t` plus the Hölder remainder. -/
private theorem smooth_part_succ_le_linearization_add_holder_error
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0)
    {v Gv : NNReal} {D : ℝ}
    (hf_holder :
      HolderGradientOn v Gv problem.feasibleSet problem.smoothPart method.gradient)
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (t : ℕ) :
    problem.smoothPart (method (t + 1)) ≤
      problem.smoothPart (method t) +
        method.gradient (method t) (method (t + 1) - method t) +
        ((Gv : ℝ) * Real.rpow D (1 + (v : ℝ)) / (1 + (v : ℝ)) *
          Real.rpow (method.stepSize t) (1 + (v : ℝ))) := by
  let τ := method.stepSize t
  have hτ_nonneg : 0 ≤ τ := (method.stepSize_mem_Ioc t).1.le
  have hv_nonneg : 0 ≤ (v : ℝ) := by exact_mod_cast v.2
  have hD_nonneg : 0 ≤ D := by
    have hzero := hdiam x0.property x0.property
    simpa using hzero
  have hnorm_le :
      ‖method (t + 1) - method t‖ ≤ τ * D :=
    successor_norm_le_stepSize_mul_diameter method hdiam t
  have hsmooth :=
    HolderGradientOn.upper_model hf_holder problem.feasibleSet_convex
      (x := method t) (y := method (t + 1))
      (method.iterates_mem_feasibleSet t) (method.iterates_mem_feasibleSet (t + 1))
  have hpow :
      Real.rpow ‖method (t + 1) - method t‖ (1 + (v : ℝ)) ≤
        Real.rpow (τ * D) (1 + (v : ℝ)) := by
    exact Real.rpow_le_rpow (norm_nonneg _) hnorm_le (by linarith)
  have hcoeff_nonneg : 0 ≤ (Gv : ℝ) / (1 + (v : ℝ)) := by
    exact div_nonneg (by exact_mod_cast Gv.2) (by positivity)
  have hpow_mul :
      Real.rpow (τ * D) (1 + (v : ℝ)) =
        Real.rpow τ (1 + (v : ℝ)) * Real.rpow D (1 + (v : ℝ)) := by
    simpa [mul_comm] using
      (Real.mul_rpow (x := τ) (y := D) (z := 1 + (v : ℝ)) hτ_nonneg hD_nonneg)
  have herr :
      ((Gv : ℝ) / (1 + (v : ℝ))) *
          Real.rpow ‖method (t + 1) - method t‖ (1 + (v : ℝ)) ≤
        ((Gv : ℝ) * Real.rpow D (1 + (v : ℝ)) / (1 + (v : ℝ))) *
          Real.rpow τ (1 + (v : ℝ)) := by
    calc
      ((Gv : ℝ) / (1 + (v : ℝ))) *
          Real.rpow ‖method (t + 1) - method t‖ (1 + (v : ℝ)) ≤
        ((Gv : ℝ) / (1 + (v : ℝ))) * Real.rpow (τ * D) (1 + (v : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hpow hcoeff_nonneg
      _ = ((Gv : ℝ) / (1 + (v : ℝ))) *
            (Real.rpow τ (1 + (v : ℝ)) * Real.rpow D (1 + (v : ℝ))) := by
            rw [hpow_mul]
      _ = ((Gv : ℝ) * Real.rpow D (1 + (v : ℝ)) / (1 + (v : ℝ))) *
            Real.rpow τ (1 + (v : ℝ)) := by
            ring
  -- Route correction: bound the smooth term directly at the actual successor iterate, so the
  -- minimizing-property comparison only pays the Hölder remainder once.
  linarith

/-- Helper for Theorem 6.14: the contracted subproblem minimizer gives the real-valued one-step
comparison against every feasible point. -/
private theorem objective_drop_ge_stepSize_mul_comparison_gap_sub_holderError
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0)
    {v Gv : NNReal} {D : ℝ}
    (hf_holder :
      HolderGradientOn v Gv problem.feasibleSet problem.smoothPart method.gradient)
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (t : ℕ) {x : E} (hx : x ∈ problem.feasibleSet) :
    (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
        (problem.smoothPart (method (t + 1)) +
          withTopRealPart problem.nonsmoothPart (method (t + 1))) ≥
      method.stepSize t *
          (method.gradient (method t) (method t - x) +
            withTopRealPart problem.nonsmoothPart (method t) -
            withTopRealPart problem.nonsmoothPart x) -
        ((Gv : ℝ) * Real.rpow D (1 + (v : ℝ)) / (1 + (v : ℝ)) *
          Real.rpow (method.stepSize t) (1 + (v : ℝ))) := by
  let τ := method.stepSize t
  let z : E := (1 - τ) • method t + τ • x
  have hτ_pos : 0 < τ := (method.stepSize_mem_Ioc t).1
  have hτ_nonneg : 0 ≤ τ := hτ_pos.le
  have hτ_le_one : τ ≤ 1 := (method.stepSize_mem_Ioc t).2
  have h_one_sub_nonneg : 0 ≤ 1 - τ := sub_nonneg.mpr hτ_le_one
  have hsum_tau : 1 - τ + τ = 1 := by ring
  have hz_mem : z ∈ problem.feasibleSet := by
    -- The comparison point is the contracted feasible combination of `x_t` and the test point.
    simpa [z, AffineMap.lineMap_apply_module] using
      problem.feasibleSet_convex.lineMap_mem
        (method.iterates_mem_feasibleSet t) hx ⟨hτ_nonneg, hτ_le_one⟩
  have hz_contracted :
      z ∈ contractedFeasibleSet problem.feasibleSet (method t) τ := by
    -- This is the exact candidate used in the minimizing-property comparison.
    exact mem_contractedFeasibleSet_iff.mpr ⟨x, hx, by simp [z]⟩
  have hnext_dom :
      method (t + 1) ∈ dom problem.nonsmoothPart :=
    problem.nonsmoothPart_closedConvex.subset_withTopEffectiveDomain
      (method.iterates_mem_feasibleSet (t + 1))
  have hz_dom :
      z ∈ dom problem.nonsmoothPart :=
    problem.nonsmoothPart_closedConvex.subset_withTopEffectiveDomain hz_mem
  have hmin_withTop :=
    (isMinOn_iff.mp (method.iterates_succ_mem_and_isMinOn t).2) z hz_contracted
  have hmin_withTop' :
      ((method.gradient (method t) (method (t + 1)) : ℝ) : WithTop ℝ) +
          problem.nonsmoothPart (method (t + 1)) ≤
        ((method.gradient (method t) z : ℝ) : WithTop ℝ) +
          problem.nonsmoothPart z := by
    simpa [_root_.compositeObjective, ContractedFeasibleSetTrustRegionScheme.gradient]
      using hmin_withTop
  rw [← coe_withTopRealPart hnext_dom, ← coe_withTopRealPart hz_dom] at hmin_withTop'
  have hmin_real_coe :
      (((withTopRealPart problem.nonsmoothPart (method (t + 1)) +
            method.gradient (method t) (method (t + 1)) : ℝ) : WithTop ℝ)) ≤
        (((withTopRealPart problem.nonsmoothPart z +
            method.gradient (method t) z : ℝ) : WithTop ℝ)) := by
    -- Read the minimizing property on the finite real surface of the nonsmooth term.
    simpa [_root_.compositeObjective, ContractedFeasibleSetTrustRegionScheme.gradient,
      add_assoc, add_left_comm, add_comm] using hmin_withTop'
  have hmin_real :
      withTopRealPart problem.nonsmoothPart (method (t + 1)) +
          method.gradient (method t) (method (t + 1)) ≤
        withTopRealPart problem.nonsmoothPart z + method.gradient (method t) z := by
    exact_mod_cast hmin_real_coe
  have hshifted_min :
      method.gradient (method t) (method (t + 1) - method t) +
          withTopRealPart problem.nonsmoothPart (method (t + 1)) ≤
        method.gradient (method t) (z - method t) + withTopRealPart problem.nonsmoothPart z := by
    -- Subtract the common constant linear term `g_t x_t` from both sides.
    have hleft :
        method.gradient (method t) (method (t + 1) - method t) =
          method.gradient (method t) (method (t + 1)) -
            method.gradient (method t) (method t) := by
      simp
    have hright :
        method.gradient (method t) (z - method t) =
          method.gradient (method t) z - method.gradient (method t) (method t) := by
      simp
    rw [hleft, hright]
    linarith
  have hz_linear :
      method.gradient (method t) (z - method t) =
        τ * method.gradient (method t) (x - method t) := by
    -- The contracted candidate moves from `x_t` toward `x` by the scalar factor `τ_t`.
    have hz_sub : z - method t = τ • (x - method t) := by
      simp [z, sub_eq_add_neg, smul_add, add_smul, add_assoc, add_left_comm, add_comm]
    rw [hz_sub]
    simp [τ]
  have hpsi :
      withTopRealPart problem.nonsmoothPart z ≤
        (1 - τ) * withTopRealPart problem.nonsmoothPart (method t) +
          τ * withTopRealPart problem.nonsmoothPart x := by
    -- Convexity of the finite real part controls the nonsmooth term at the contracted point.
    simpa [z] using
      problem.nonsmoothPart_closedConvex.convexOn_withTopRealPart.2
        (method.iterates_mem_feasibleSet t) hx h_one_sub_nonneg hτ_nonneg hsum_tau
  have hcomparison :
      method.gradient (method t) (method (t + 1) - method t) +
          withTopRealPart problem.nonsmoothPart (method (t + 1)) ≤
        τ * method.gradient (method t) (x - method t) +
          (1 - τ) * withTopRealPart problem.nonsmoothPart (method t) +
          τ * withTopRealPart problem.nonsmoothPart x := by
    -- Combine the minimizing-property comparison with the convexity estimate at `z`.
    rw [hz_linear] at hshifted_min
    have hpsi_shift :
        τ * method.gradient (method t) (x - method t) +
            withTopRealPart problem.nonsmoothPart z ≤
          τ * method.gradient (method t) (x - method t) +
            (1 - τ) * withTopRealPart problem.nonsmoothPart (method t) +
            τ * withTopRealPart problem.nonsmoothPart x := by
      linarith
    exact hshifted_min.trans hpsi_shift
  have hgrad_neg :
      method.gradient (method t) (method t - x) =
        -method.gradient (method t) (x - method t) := by
    -- Normalize the comparison gap to the `x_t - x` convention used on the theorem surface.
    simp
  have hpsi_drop :
      withTopRealPart problem.nonsmoothPart (method t) -
          withTopRealPart problem.nonsmoothPart (method (t + 1)) ≥
        τ *
            (method.gradient (method t) (method t - x) +
              withTopRealPart problem.nonsmoothPart (method t) -
              withTopRealPart problem.nonsmoothPart x) +
          method.gradient (method t) (method (t + 1) - method t) := by
    -- Rearrange the minimizing-property inequality into the exact nonsmooth-drop form.
    rw [hgrad_neg]
    linarith
  have hsmooth :=
    smooth_part_succ_le_linearization_add_holder_error method hf_holder hdiam t
  -- Add the smooth decrease estimate to the rearranged nonsmooth drop.
  linarith

/-- Helper for Theorem 6.14: multiplying the one-step comparison by `A_{t+1}` yields the exact
weighted successor inequality used in the induction for `A_t \bar f(x_t) ≤ φ_t(x) + C_{v,t}`. -/
private lemma weighted_objective_step_bound
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0)
    (a : ℕ → ℝ) {v Gv : NNReal} {D : ℝ}
    (hf_holder :
      HolderGradientOn v Gv problem.feasibleSet problem.smoothPart method.gradient)
    (ha_pos : ∀ t : ℕ, 0 < a t)
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (t : ℕ) {x : E} (hx : x ∈ problem.feasibleSet) :
    accumulatedWeights a (t + 1) *
        (problem.smoothPart (method (t + 1)) +
          withTopRealPart problem.nonsmoothPart (method (t + 1))) ≤
      accumulatedWeights a t *
          (problem.smoothPart (method t) +
            withTopRealPart problem.nonsmoothPart (method t)) +
        a (t + 1) *
          (problem.smoothPart (method t) +
            method.gradient (method t) (x - method t) +
            withTopRealPart problem.nonsmoothPart x) +
        (Real.rpow (a (t + 1)) (1 + (v : ℝ)) /
            Real.rpow (accumulatedWeights a (t + 1)) (v : ℝ)) *
          ((Gv : ℝ) / (1 + (v : ℝ))) * Real.rpow D (1 + (v : ℝ)) := by
  let u :=
    problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)
  let w :=
    problem.smoothPart (method t) +
      method.gradient (method t) (x - method t) +
      withTopRealPart problem.nonsmoothPart x
  have hA_pos : 0 < accumulatedWeights a (t + 1) := accumulatedWeights_pos a ha_pos (t + 1)
  have hA_nonneg : 0 ≤ accumulatedWeights a (t + 1) := hA_pos.le
  have hτ_pos : 0 < method.stepSize t := (method.stepSize_mem_Ioc t).1
  have hτ_pow :
      method.stepSize t * Real.rpow (method.stepSize t) (v : ℝ) =
        Real.rpow (method.stepSize t) (1 + (v : ℝ)) := by
    -- Merge the explicit `τ_t` factor with the Hölder power `τ_t^v`.
    simpa [Real.rpow_one] using (Real.rpow_add hτ_pos 1 (v : ℝ)).symm
  have herr_split :
      method.stepSize t *
          (((Gv : ℝ) / (1 + (v : ℝ))) * Real.rpow D (1 + (v : ℝ)) *
            Real.rpow (method.stepSize t) (v : ℝ)) =
        ((Gv : ℝ) * Real.rpow D (1 + (v : ℝ)) / (1 + (v : ℝ)) *
          Real.rpow (method.stepSize t) (1 + (v : ℝ))) := by
    -- This is the exact factorization needed to rewrite the one-step Hölder remainder as
    -- `τ_t * δ_t`.
    calc
      method.stepSize t *
          (((Gv : ℝ) / (1 + (v : ℝ))) * Real.rpow D (1 + (v : ℝ)) *
            Real.rpow (method.stepSize t) (v : ℝ)) =
        ((Gv : ℝ) / (1 + (v : ℝ))) * Real.rpow D (1 + (v : ℝ)) *
          (method.stepSize t * Real.rpow (method.stepSize t) (v : ℝ)) := by
            ring
      _ =
        ((Gv : ℝ) / (1 + (v : ℝ))) * Real.rpow D (1 + (v : ℝ)) *
          Real.rpow (method.stepSize t) (1 + (v : ℝ)) := by
            rw [hτ_pow]
      _ =
        ((Gv : ℝ) * Real.rpow D (1 + (v : ℝ)) / (1 + (v : ℝ)) *
          Real.rpow (method.stepSize t) (1 + (v : ℝ))) := by
            ring
  have hnormalized_raw :=
    objective_drop_ge_stepSize_mul_comparison_gap_sub_holderError method hf_holder hdiam t hx
  have hnormalized :
      problem.smoothPart (method (t + 1)) +
          withTopRealPart problem.nonsmoothPart (method (t + 1)) ≤
        (1 - method.stepSize t) * u +
          method.stepSize t *
            (w +
              (((Gv : ℝ) / (1 + (v : ℝ))) * Real.rpow D (1 + (v : ℝ)) *
                Real.rpow (method.stepSize t) (v : ℝ))) := by
    -- Route correction: rewrite the real drop theorem into the normalized convex-combination
    -- form before multiplying by `A_{t+1}`.
    rw [show
        ((1 - method.stepSize t) * u +
            method.stepSize t *
              (w +
                (((Gv : ℝ) / (1 + (v : ℝ))) * Real.rpow D (1 + (v : ℝ)) *
                  Real.rpow (method.stepSize t) (v : ℝ))) :
            ℝ) =
          ((1 - method.stepSize t) * u + method.stepSize t * w) +
            method.stepSize t *
              (((Gv : ℝ) / (1 + (v : ℝ))) * Real.rpow D (1 + (v : ℝ)) *
                Real.rpow (method.stepSize t) (v : ℝ)) by
          ring]
    rw [show
        ((1 - method.stepSize t) * u + method.stepSize t * w : ℝ) =
          u - method.stepSize t *
            (method.gradient (method t) (method t - x) +
              withTopRealPart problem.nonsmoothPart (method t) -
              withTopRealPart problem.nonsmoothPart x) by
          have hgrad_flip :
              method.gradient (method t) (method t - x) =
                -method.gradient (method t) (x - method t) := by
            simp
          rw [hgrad_flip]
          dsimp [u, w]
          ring]
    rw [herr_split]
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hnormalized hA_nonneg
  rw [h_step t] at hscaled
  let delta :=
    ((Gv : ℝ) / (1 + (v : ℝ))) * Real.rpow D (1 + (v : ℝ)) *
      Real.rpow (τ[a](t)) (v : ℝ)
  have hsplit :
      accumulatedWeights a (t + 1) *
          ((1 - τ[a](t)) * u + τ[a](t) * (w + delta)) =
        accumulatedWeights a (t + 1) * ((1 - τ[a](t)) * u + τ[a](t) * w) +
          accumulatedWeights a (t + 1) * (τ[a](t) * delta) := by
    -- Split the successor affine term from the single Hölder increment before the rescaling
    -- lemmas rewrite `τ_t` into `a_{t+1} / A_{t+1}`.
    ring
  rw [show
      (((Gv : ℝ) / (1 + (v : ℝ))) * Real.rpow D (1 + (v : ℝ)) *
          Real.rpow (τ[a](t)) (v : ℝ) : ℝ) = delta by
        rfl] at hscaled
  rw [hsplit] at hscaled
  rw [successor_weighted_average_rescaling (a := a) ha_pos t u w,
    weight_coefficient_holder_rescaling (a := a) ha_pos (v := (v : ℝ)) (Gv := (Gv : ℝ))
      (D := D) t] at hscaled
  simpa [u, w, delta] using hscaled

/- Theorem 6.14 lies in the Chapter 6 contracted conditional-gradient / estimating-sequence
domain.

Mandatory domain-style sampling:
- `accumulatedWeights` / `weightCoefficient` in `Definition_6_53`, the chapter owners of
  `A[a](t)` and `τ[a](t)`;
- `ContractedFeasibleSetTrustRegionScheme` in `Algorithm_6_5`, the source-facing owner of the
  iterate, step-size, and contracted-subproblem data;
- `linearizedCompositeGap` in this file, the chosen-dual Chapter 6 gap owner attached to the
  actual linear model used by Algorithm 6.5;
- `linearModelTotalVariation` in `Definition_6_59`, the Chapter 6 owner `δ[Q, f, Ψ](x)` of the
  ambient-gradient total variation at a feasible point;
- `linearOptimizationOracleErrorBound` in `Definition_6_53`, the canonical Chapter 6 owner whose
  specialization here is the source-facing error term `C_{v,t}`;
- `HolderGradientOn.upper_model` in `Proposition_6_39`, the nearby Hölder upper-model bridge used
  to control the smooth remainder.

Best owner abstraction:
- source-facing: Theorem 6.14's weighted estimating-function bound and the one-step decrease
  bound written with the chosen-dual gap `linearizedCompositeGap`;
- core/canonical: `ContractedFeasibleSetTrustRegionScheme`, `A[a](t)`, `τ[a](t)`,
  `linearOptimizationOracleErrorBound`, `HolderGradientOn`, and the ambient-gradient owner
  `linearModelTotalVariation`;
- bridge/view: `linearModelTotalVariation_eq_linearizedCompositeGap`, which identifies the
  chosen-dual owner with `δ[Q, f, Ψ](x)` only under an explicit ambient-gradient specialization.

Primitive data:
- the ambient composite problem and Algorithm 6.5 method data;
- the weight sequence `a`, together with the positivity condition `∀ t, 0 < a t` and the
  canonical coefficient identity `method.stepSize t = τ[a](t)`;
- the Hölder-gradient owner `HolderGradientOn` and the feasible-set diameter bound.

Derived API:
- the specialized estimating sequence `estimatingFunction`;
- the theorem-surface notation `φ[method, a, \tilde f](t, x)` for that specialized sequence;
- the source-facing Chapter 6 error term `contractionErrorTerm`, together with the theorem-surface
  notation `C[Δ₀, a, Gᵥ, D, v](t)`, both derived from `linearOptimizationOracleErrorBound`;
- the weighted objective upper bound, the chosen-dual decrease estimate below, and its ambient-
  gradient specialization through `linearModelTotalVariation_eq_linearizedCompositeGap`.

Source/core/bridge triage:
- source-facing: the two statements of Theorem 6.14;
- core/canonical: the chapter owners listed above, with Theorem 6.14 (2) surfaced through the
  actual chosen-dual linear model carried by `method.gradient`;
- bridge/view: `linearizedCompositeGap`, whose defining body is exactly the canonical
  `restrictedDualFunction` bridge, and `linearModelTotalVariation_eq_linearizedCompositeGap`,
  which specializes that chosen-dual owner to `δ[Q, f, Ψ](x_t)` when the ambient gradient really
  matches the chosen field.
-/

-- Proof sketch: prove the estimate by induction on `t`. For the induction step, unfold
-- `ContractedFeasibleSetTrustRegionScheme.estimatingFunction`, apply the contracted-subproblem
-- minimizing property from `Algorithm_6_5` at step `t` to the contracted point determined by the
-- comparison vector `x ∈ Q`, then use the Hölder upper-model bound coming from `hf_holder`
-- together with the positive-weight hypothesis `ha_pos`, the diameter bound `hdiam`, and the
-- weight identity `τ_t = a_{t+1} / A_{t+1}` to absorb the remainder into
-- `contractionErrorTerm`.
/-- Theorem 6.14 (1): along Algorithm 6.5, if the initial model `\tilde f` underestimates the
initial objective up to the scalar initial-gap term `Δ(x₀)` and the weights satisfy `a_t > 0`,
then for every Hölder exponent parameter `v : NNReal`, every index `t ≥ 0`, and every
comparison point `x ∈ Q`, one has
`A_t \bar f(x_t) ≤ φ_t(x) + C_{v,t}`. -/
theorem weighted_objective_le_estimatingFunction_add_contractionError
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0)
    (a : ℕ → ℝ) (tildeF : E → ℝ) (Δ0 : ℝ) {v Gv : NNReal} {D : ℝ}
    (hinitial :
      ∀ ⦃x : E⦄, x ∈ problem.feasibleSet →
        problem.smoothPart x0 + withTopRealPart problem.nonsmoothPart x0 ≤ tildeF x + Δ0)
    (hf_holder :
      HolderGradientOn v Gv problem.feasibleSet problem.smoothPart method.gradient)
    (ha_pos : ∀ t : ℕ, 0 < a t)
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (t : ℕ) {x : E} (hx : x ∈ problem.feasibleSet) :
      A[a](t) *
          (problem.smoothPart (method t) +
            withTopRealPart problem.nonsmoothPart (method t)) ≤
        φ[method, a, tildeF](t, x) +
          C[Δ0, a, (Gv : ℝ), D, (v : ℝ)](t) := by
  induction t with
  | zero =>
      have ha0_nonneg : 0 ≤ a 0 := (ha_pos 0).le
      have hbase := mul_le_mul_of_nonneg_left (hinitial hx) ha0_nonneg
      -- The initial stage is exactly the scaled starting underestimator plus the initial
      -- `a₀ Δ₀` error contribution.
      calc
        A[a](0) *
            (problem.smoothPart (method 0) +
              withTopRealPart problem.nonsmoothPart (method 0)) ≤
          a 0 * (tildeF x + Δ0) := by
            simpa [accumulatedWeights_apply,
              ContractedFeasibleSetTrustRegionScheme.estimatingFunction,
              estimatingFunctionalSequence] using hbase
        _ =
          φ[method, a, tildeF](0, x) +
            C[Δ0, a, (Gv : ℝ), D, (v : ℝ)](0) := by
              simp [ContractedFeasibleSetTrustRegionScheme.estimatingFunction,
                estimatingFunctionalSequence, contractionErrorTerm,
                linearOptimizationOracleErrorBound_def, mul_add, add_comm, add_left_comm,
                add_assoc]
  | succ t ih =>
      have hstep :=
        weighted_objective_step_bound
          (method := method) (a := a) (hf_holder := hf_holder)
          (ha_pos := ha_pos) (h_step := h_step) (hdiam := hdiam) t hx
      have hcombine :
          A[a](t) *
              (problem.smoothPart (method t) +
                withTopRealPart problem.nonsmoothPart (method t)) +
            a (t + 1) *
              (problem.smoothPart (method t) +
                method.gradient (method t) (x - method t) +
                withTopRealPart problem.nonsmoothPart x) +
            (Real.rpow (a (t + 1)) (1 + (v : ℝ)) /
                Real.rpow (accumulatedWeights a (t + 1)) (v : ℝ)) *
              ((Gv : ℝ) / (1 + (v : ℝ))) * Real.rpow D (1 + (v : ℝ)) ≤
            φ[method, a, tildeF](t, x) + C[Δ0, a, (Gv : ℝ), D, (v : ℝ)](t) +
              a (t + 1) *
                (problem.smoothPart (method t) +
                  method.gradient (method t) (x - method t) +
                  withTopRealPart problem.nonsmoothPart x) +
              (Real.rpow (a (t + 1)) (1 + (v : ℝ)) /
                  Real.rpow (accumulatedWeights a (t + 1)) (v : ℝ)) *
                ((Gv : ℝ) / (1 + (v : ℝ))) * Real.rpow D (1 + (v : ℝ)) := by
        -- Add the induction hypothesis to the new affine model term and the new Hölder
        -- increment.
        linarith
      calc
        accumulatedWeights a (t + 1) *
            (problem.smoothPart (method (t + 1)) +
              withTopRealPart problem.nonsmoothPart (method (t + 1))) ≤
          accumulatedWeights a t *
              (problem.smoothPart (method t) +
                withTopRealPart problem.nonsmoothPart (method t)) +
            a (t + 1) *
              (problem.smoothPart (method t) +
                method.gradient (method t) (x - method t) +
                withTopRealPart problem.nonsmoothPart x) +
            (Real.rpow (a (t + 1)) (1 + (v : ℝ)) /
                Real.rpow (accumulatedWeights a (t + 1)) (v : ℝ)) *
              ((Gv : ℝ) / (1 + (v : ℝ))) * Real.rpow D (1 + (v : ℝ)) := hstep
        _ ≤
          φ[method, a, tildeF](t, x) + C[Δ0, a, (Gv : ℝ), D, (v : ℝ)](t) +
            a (t + 1) *
              (problem.smoothPart (method t) +
                method.gradient (method t) (x - method t) +
                withTopRealPart problem.nonsmoothPart x) +
            (Real.rpow (a (t + 1)) (1 + (v : ℝ)) /
                Real.rpow (accumulatedWeights a (t + 1)) (v : ℝ)) *
              ((Gv : ℝ) / (1 + (v : ℝ))) * Real.rpow D (1 + (v : ℝ)) := hcombine
        _ =
          ContractedFeasibleSetTrustRegionScheme.estimatingFunction method a tildeF (t + 1) x +
            contractionErrorTerm Δ0 a (Gv : ℝ) D (v : ℝ) (t + 1) := by
              -- Unfold the estimating-sequence and error-term recursions at the successor index.
              rw [contractionErrorTerm_succ]
              simp [ContractedFeasibleSetTrustRegionScheme.estimatingFunction,
                estimatingFunctionalSequence, contractionErrorTerm, add_assoc, add_left_comm,
                add_comm]

/-- Helper for Theorem 6.14: a pointwise real affine-gap bound packages directly into an upper
bound for `linearizedCompositeGap S Ψ s x₀`. -/
private lemma linearizedCompositeGap_le_of_real_bound
    {S : Set E} (Ψ : E → ℝ) (s : StrongDual ℝ E) (x0 : S) {B : ℝ}
    (hB : ∀ y : E, y ∈ S → s ((x0 : E) - y) + Ψ x0 - Ψ y ≤ B) :
    linearizedCompositeGap S Ψ s x0 ≤ (B : EReal) := by
  -- Rewrite the chosen-dual gap as the explicit feasible-point supremum and bound each term by
  -- the common real constant `B`.
  simp only [linearizedCompositeGap]
  refine sSup_le ?_
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  show (((s ((x0 : E) - x) + Ψ x0 - Ψ x : ℝ) : EReal)) ≤ (B : EReal)
  exact_mod_cast hB x hx

section LinearizedCompositeGapObjectiveDrop

-- Proof sketch: compare `x_{t+1}` with the contracted candidate `(1 - τ_t) x_t + τ_t y` in the
-- local minimizing property, identify the best comparison over `y ∈ Q` with the chosen-dual gap
-- `linearizedCompositeGap problem.feasibleSet (withTopRealPart problem.nonsmoothPart)
--   (method.gradient (method t)) (method.iterates t)`,
-- and then use the Hölder upper-model estimate from `hf_holder` plus the diameter control
-- `hdiam` to bound the remainder by
-- `(G_v D^(1+v) / (1+v)) τ_t^(1+v)`.
/-- Theorem 6.14 (2): at every step of Algorithm 6.5, the composite-objective decrease
`\bar f(x_t) - \bar f(x_{t+1})` is bounded below by the step size times the chosen-dual
linearized composite gap attached to the actual linear model used at `x_t`, minus the Hölder
remainder
`(G_v D^(1+v) / (1 + v)) τ_t^(1+v)`. -/
theorem objective_drop_ge_stepSize_mul_linearizedCompositeGap_sub_holderError
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) {v Gv : NNReal} {D : ℝ}
    (hf_holder :
      HolderGradientOn v Gv problem.feasibleSet problem.smoothPart method.gradient)
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (t : ℕ) :
      (((problem.smoothPart (method t) +
            withTopRealPart problem.nonsmoothPart (method t)) -
          (problem.smoothPart (method (t + 1)) +
            withTopRealPart problem.nonsmoothPart (method (t + 1))) : ℝ) : EReal) ≥
        (method.stepSize t : EReal) *
            linearizedCompositeGap problem.feasibleSet
              (withTopRealPart problem.nonsmoothPart) (method.gradient (method t))
              (method.iterates t) -
          (((Gv : ℝ) * Real.rpow D (1 + (v : ℝ)) / (1 + (v : ℝ)) *
              Real.rpow (method.stepSize t) (1 + (v : ℝ)) : ℝ) : EReal) := by
  let drop : ℝ :=
    (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
      (problem.smoothPart (method (t + 1)) +
        withTopRealPart problem.nonsmoothPart (method (t + 1)))
  let err : ℝ :=
    ((Gv : ℝ) * Real.rpow D (1 + (v : ℝ)) / (1 + (v : ℝ)) *
      Real.rpow (method.stepSize t) (1 + (v : ℝ)))
  have hτ_pos : 0 < method.stepSize t := (method.stepSize_mem_Ioc t).1
  have hτE_pos : 0 < (method.stepSize t : EReal) := by
    exact_mod_cast hτ_pos
  have hτE_top : (method.stepSize t : EReal) ≠ ⊤ := by
    simp
  have hgap_div :
      linearizedCompositeGap problem.feasibleSet
          (withTopRealPart problem.nonsmoothPart) (method.gradient (method t))
          (method.iterates t) ≤
        ((((drop + err) / method.stepSize t : ℝ) : EReal)) := by
    -- Package the pointwise real drop estimate into a single upper bound on the chosen-dual gap.
    refine linearizedCompositeGap_le_of_real_bound
      (Ψ := withTopRealPart problem.nonsmoothPart)
      (s := method.gradient (method t)) (x0 := method.iterates t) ?_
    intro y hy
    have hy_drop :=
      objective_drop_ge_stepSize_mul_comparison_gap_sub_holderError method hf_holder hdiam t hy
    dsimp [drop, err] at hy_drop ⊢
    exact (le_div_iff₀ hτ_pos).2 (by linarith)
  have hmul :
      linearizedCompositeGap problem.feasibleSet
          (withTopRealPart problem.nonsmoothPart) (method.gradient (method t))
          (method.iterates t) * (method.stepSize t : EReal) ≤
        (drop : EReal) + (err : EReal) := by
    -- Move from the divided real bound to the scaled `EReal` bound by the positive
    -- order-isomorphism `z ↦ z * τ_t`.
    have hgap_div' :
        linearizedCompositeGap problem.feasibleSet
            (withTopRealPart problem.nonsmoothPart) (method.gradient (method t))
            (method.iterates t) ≤
          ((drop : EReal) + (err : EReal)) / (method.stepSize t : EReal) := by
      simpa [EReal.coe_div, EReal.coe_add] using hgap_div
    exact (EReal.le_div_iff_mul_le hτE_pos hτE_top).1 hgap_div'
  have hsub :
      (method.stepSize t : EReal) *
            linearizedCompositeGap problem.feasibleSet
              (withTopRealPart problem.nonsmoothPart) (method.gradient (method t))
              (method.iterates t) -
          (err : EReal) ≤
        (drop : EReal) := by
    -- Rewrite the scaled gap estimate into the target lower-bound shape by moving the error term
    -- to the left.
    exact EReal.sub_le_of_le_add (by simpa [add_comm, mul_comm] using hmul)
  simpa [drop, err, mul_comm] using hsub

end LinearizedCompositeGapObjectiveDrop

section TotalVariationObjectiveDrop

variable [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: apply the chosen-dual decrease theorem above and then rewrite the gap term by the
-- supplied identification with the Chapter 6 total-variation owner. This identification is the
-- one induced, for example, by `linearModelTotalVariation_eq_linearizedCompositeGap` when the
-- chosen derivative field really is the ambient gradient at `x_t`.
/-- Under the additional hypothesis that the chosen-dual gap used by Algorithm 6.5 agrees at
`x_t` with the Chapter 6 total-variation owner `δ[Q, f, Ψ](x_t)` (for instance because the chosen
derivative field agrees there with the ambient gradient), Theorem 6.14 (2) specializes to the
ambient-gradient total-variation form. -/
theorem objective_drop_ge_stepSize_mul_totalVariation_sub_holderError
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) {v Gv : NNReal} {D : ℝ}
    (hf_holder :
      HolderGradientOn v Gv problem.feasibleSet problem.smoothPart method.gradient)
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (t : ℕ)
    (hgap :
      linearizedCompositeGap problem.feasibleSet
          (withTopRealPart problem.nonsmoothPart) (method.gradient (method t))
          (method.iterates t) =
        δ[problem.feasibleSet, problem.smoothPart,
          withTopRealPart problem.nonsmoothPart]((method.iterates t))) :
      (((problem.smoothPart (method t) +
            withTopRealPart problem.nonsmoothPart (method t)) -
          (problem.smoothPart (method (t + 1)) +
            withTopRealPart problem.nonsmoothPart (method (t + 1))) : ℝ) : EReal) ≥
        (method.stepSize t : EReal) *
            (δ[problem.feasibleSet, problem.smoothPart,
              withTopRealPart problem.nonsmoothPart]((method.iterates t))) -
          (((Gv : ℝ) * Real.rpow D (1 + (v : ℝ)) / (1 + (v : ℝ)) *
              Real.rpow (method.stepSize t) (1 + (v : ℝ)) : ℝ) : EReal) := by
  have hdrop :=
    objective_drop_ge_stepSize_mul_linearizedCompositeGap_sub_holderError
      method hf_holder hdiam t
  simpa [hgap] using hdrop

end TotalVariationObjectiveDrop

end ConditionalGradientContraction

end
