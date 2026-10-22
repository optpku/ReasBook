/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_19
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_16
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Proposition 5.16 is `source-facing`: it records the strong-convexity modulus of the concrete
extended-real-valued ball-pen function from Example 5.29 on Euclidean `ℝ^n`. The Chapter 4
function `negative_sqrt_one_sub_norm_sq_extension` already provides the source-specified owner, so
this file states the proposition directly for that owner using the Chapter 5 source-facing
predicate `is_strongly_convex_function`.
-/

-- Proof sketch: use Proposition 4.19's explicit extended-real-valued owner and verify the
-- defining segment inequality on its effective domain `{x : E | ‖x‖ ≤ 1}`, where the function
-- agrees with `x ↦ -√(1 - ‖x‖²)`. The source-facing strong-convexity class then packages the
-- convex effective domain, the no-`⊥` property, and the modulus `1`.
/-- Helper for Proposition 5.16: the ball-pen extension never takes the value `-∞`. -/
private theorem negativeSqrtOneSubNormSqExtension_neBot (x : E) :
    (negative_sqrt_one_sub_norm_sq_extension : E → EReal) x ≠ ⊥ := by
  -- Split into the finite closed-ball branch and the exterior `∞` branch.
  by_cases hx : ‖x‖ ≤ 1
  · rw [negative_sqrt_one_sub_norm_sq_extension_of_norm_le_one hx]
    exact EReal.coe_ne_bot _
  · rw [negative_sqrt_one_sub_norm_sq_extension_of_one_lt_norm (lt_of_not_ge hx)]
    simp

/-- Helper for Proposition 5.16: membership in the effective domain of the ball-pen extension is
equivalent to belonging to the closed unit ball. -/
private theorem memEffectiveDomain_negativeSqrtOneSubNormSqExtension_iff {x : E} :
    x ∈ effective_domain (negative_sqrt_one_sub_norm_sq_extension : E → EReal) ↔
      x ∈ Metric.closedBall (0 : E) 1 := by
  -- The Chapter 4 owner is finite exactly on the branch `‖x‖ ≤ 1`.
  rw [mem_effective_domain, mem_closedBall_zero_iff]
  by_cases hx : ‖x‖ ≤ 1
  · rw [negative_sqrt_one_sub_norm_sq_extension_of_norm_le_one hx]
    simpa [hx] using (EReal.coe_lt_top (-Real.sqrt (1 - ‖x‖ ^ (2 : ℕ))))
  · rw [negative_sqrt_one_sub_norm_sq_extension_of_one_lt_norm (lt_of_not_ge hx)]
    simp [hx]

/-- Helper for Proposition 5.16: the effective domain of the ball-pen extension is the closed unit
ball. -/
private theorem effectiveDomain_negativeSqrtOneSubNormSqExtension :
    effective_domain (negative_sqrt_one_sub_norm_sq_extension : E → EReal) =
      Metric.closedBall (0 : E) 1 := by
  -- Upgrade the pointwise domain characterization to an equality of sets.
  ext x
  exact memEffectiveDomain_negativeSqrtOneSubNormSqExtension_iff

/-- Helper for Proposition 5.16: the scalar shifted ball-pen profile
`t ↦ -Real.sqrt (1 - t) - t / 2` is convex on `[0, 1]`. -/
private theorem ballPenShiftedProfile_convexOn :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ ↦ -Real.sqrt (1 - t) - t / 2) := by
  let oneSubAffine : ℝ →ᵃ[ℝ] ℝ := AffineMap.const ℝ ℝ 1 - AffineMap.id ℝ ℝ
  have hsqrt :
      ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ ↦ Real.sqrt (1 - t)) := by
    have hsqrt_preimage :
        ConcaveOn ℝ (oneSubAffine ⁻¹' Set.Ici (0 : ℝ))
          (fun t : ℝ ↦ Real.sqrt (oneSubAffine t)) := by
      -- Compose the standard concavity of `sqrt` with the affine map `t ↦ 1 - t`.
      simpa [oneSubAffine] using
        (Real.strictConcaveOn_sqrt.concaveOn.comp_affineMap oneSubAffine)
    have hsubset : Set.Icc (0 : ℝ) 1 ⊆ oneSubAffine ⁻¹' Set.Ici (0 : ℝ) := by
      intro t ht
      simpa [oneSubAffine] using sub_nonneg.mpr ht.2
    exact hsqrt_preimage.subset hsubset (convex_Icc (0 : ℝ) 1)
  have hhalfId :
      ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ ↦ t / 2) := by
    have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by
      norm_num
    -- The linear part is affine, hence convex.
    simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
      (convexOn_id (convex_Icc (0 : ℝ) 1)).smul hhalf_nonneg
  have hhalfIdConcave :
      ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ ↦ t / 2) := by
    have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by
      norm_num
    -- The same affine function is concave as well.
    simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
      (concaveOn_id (convex_Icc (0 : ℝ) 1)).smul hhalf_nonneg
  -- Negating the concave radical and subtracting the affine term yields a convex profile.
  simpa [sub_eq_add_neg] using hsqrt.neg.add hhalfIdConcave.neg

/-- Helper for Proposition 5.16: the scalar shifted ball-pen profile is monotone on `[0, 1]`. -/
private theorem ballPenShiftedProfile_monotoneOn :
    MonotoneOn (fun t : ℝ ↦ -Real.sqrt (1 - t) - t / 2) (Set.Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  have hsa_nonneg : 0 ≤ Real.sqrt (1 - a) - Real.sqrt (1 - b) := by
    apply sub_nonneg.mpr
    apply Real.sqrt_monotone
    linarith
  have hsqrt_sum_le_two : Real.sqrt (1 - a) + Real.sqrt (1 - b) ≤ 2 := by
    have hsa_le_one : Real.sqrt (1 - a) ≤ 1 := by
      exact (Real.sqrt_le_one).2 (sub_le_self 1 ha.1)
    have hsb_le_one : Real.sqrt (1 - b) ≤ 1 := by
      exact (Real.sqrt_le_one).2 (sub_le_self 1 hb.1)
    linarith
  have hsqrt_gap :
      (b - a) / 2 ≤ Real.sqrt (1 - a) - Real.sqrt (1 - b) := by
    have hfactor :
        b - a =
          (Real.sqrt (1 - a) - Real.sqrt (1 - b)) *
            (Real.sqrt (1 - a) + Real.sqrt (1 - b)) := by
      calc
        b - a = (1 - a) - (1 - b) := by ring
        _ = Real.sqrt (1 - a) ^ (2 : ℕ) - Real.sqrt (1 - b) ^ (2 : ℕ) := by
            rw [Real.sq_sqrt (sub_nonneg.mpr ha.2), Real.sq_sqrt (sub_nonneg.mpr hb.2)]
        _ = (Real.sqrt (1 - a) + Real.sqrt (1 - b)) *
              (Real.sqrt (1 - a) - Real.sqrt (1 - b)) := by
            rw [sq_sub_sq]
        _ = (Real.sqrt (1 - a) - Real.sqrt (1 - b)) *
              (Real.sqrt (1 - a) + Real.sqrt (1 - b)) := by
            ring
    have hmul :
        b - a ≤ (Real.sqrt (1 - a) - Real.sqrt (1 - b)) * 2 := by
      calc
        b - a =
            (Real.sqrt (1 - a) - Real.sqrt (1 - b)) *
              (Real.sqrt (1 - a) + Real.sqrt (1 - b)) := hfactor
        _ ≤ (Real.sqrt (1 - a) - Real.sqrt (1 - b)) * 2 := by
            gcongr
    nlinarith
  -- Rewrite the target inequality into the square-root gap estimate above.
  nlinarith

/-- Helper for Proposition 5.16: on the closed unit ball, the real-valued barrier
`x ↦ -Real.sqrt (1 - ‖x‖ ^ (2 : ℕ))` is `1`-strongly convex. -/
private theorem ballPenStrongConvexOnClosedBall :
    StrongConvexOn (Metric.closedBall (0 : E) 1) 1
      (fun x : E ↦ -Real.sqrt (1 - ‖x‖ ^ (2 : ℕ))) := by
  rw [strongConvexOn_iff_convex]
  let s : Set E := Metric.closedBall (0 : E) 1
  let shiftedBarrier : E → ℝ :=
    fun x : E ↦ -Real.sqrt (1 - ‖x‖ ^ (2 : ℕ)) - ‖x‖ ^ (2 : ℕ) / 2
  have hs : Convex ℝ s := convex_closedBall (0 : E) 1
  have hnormSq : ConvexOn ℝ s (fun x : E ↦ ‖x‖ ^ (2 : ℕ)) := by
    -- The squared norm is convex on every convex set.
    exact (convexOn_norm hs).pow (fun x hx ↦ norm_nonneg x) 2
  have hnormSq_mem :
      ∀ {x : E}, x ∈ s → ‖x‖ ^ (2 : ℕ) ∈ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    rw [show s = Metric.closedBall (0 : E) 1 by rfl] at hx
    rw [mem_closedBall_zero_iff] at hx
    refine ⟨by positivity, ?_⟩
    have hmul : ‖x‖ * ‖x‖ ≤ 1 * 1 := by
      gcongr
    simpa [pow_two] using hmul
  have hshifted : ConvexOn ℝ s shiftedBarrier := by
    refine ⟨hs, ?_⟩
    intro x hx y hy a b ha hb hab
    have hxy_mem : a • x + b • y ∈ s := hs hx hy ha hb hab
    have hxIcc : ‖x‖ ^ (2 : ℕ) ∈ Set.Icc (0 : ℝ) 1 := hnormSq_mem hx
    have hyIcc : ‖y‖ ^ (2 : ℕ) ∈ Set.Icc (0 : ℝ) 1 := hnormSq_mem hy
    have hxyIcc : ‖a • x + b • y‖ ^ (2 : ℕ) ∈ Set.Icc (0 : ℝ) 1 := hnormSq_mem hxy_mem
    have hcomboIcc :
        a * ‖x‖ ^ (2 : ℕ) + b * ‖y‖ ^ (2 : ℕ) ∈ Set.Icc (0 : ℝ) 1 :=
      ballPenShiftedProfile_convexOn.1 hxIcc hyIcc ha hb hab
    -- First control the norm-square of the midpoint, then apply scalar convexity of the profile.
    calc
      shiftedBarrier (a • x + b • y)
          = -Real.sqrt (1 - ‖a • x + b • y‖ ^ (2 : ℕ)) -
              ‖a • x + b • y‖ ^ (2 : ℕ) / 2 := by
              rfl
      _ ≤ -Real.sqrt (1 - (a * ‖x‖ ^ (2 : ℕ) + b * ‖y‖ ^ (2 : ℕ))) -
            (a * ‖x‖ ^ (2 : ℕ) + b * ‖y‖ ^ (2 : ℕ)) / 2 := by
            exact ballPenShiftedProfile_monotoneOn hxyIcc hcomboIcc (hnormSq.2 hx hy ha hb hab)
      _ ≤ a * (-Real.sqrt (1 - ‖x‖ ^ (2 : ℕ)) - ‖x‖ ^ (2 : ℕ) / 2) +
            b * (-Real.sqrt (1 - ‖y‖ ^ (2 : ℕ)) - ‖y‖ ^ (2 : ℕ) / 2) := by
            exact ballPenShiftedProfile_convexOn.2 hxIcc hyIcc ha hb hab
      _ = a * shiftedBarrier x + b * shiftedBarrier y := by
            rfl
  -- Rewrite the shifted barrier back into the standard strong-convexity normal form.
  refine hshifted.congr ?_
  intro x hx
  simp [shiftedBarrier, sub_eq_add_neg, div_eq_mul_inv, mul_comm]

/-- Proposition 5.16: the ball-pen function from Example 5.29, represented by
`negative_sqrt_one_sub_norm_sq_extension`, is `1`-strongly convex with respect to the Euclidean
norm in the chapter's source-facing extended-real-valued sense. -/
theorem negative_sqrt_one_sub_norm_sq_extension_is_strongly_convex_function :
    is_strongly_convex_function (negative_sqrt_one_sub_norm_sq_extension : E → EReal) 1 := by
  -- Route correction: prove the real-valued closed-ball owner theorem first, then transport it
  -- through `is_strongly_convex_function_iff_strongConvexOn_toReal`.
  refine is_strongly_convex_function_iff_strongConvexOn_toReal.mpr ?_
  refine ⟨by norm_num, negativeSqrtOneSubNormSqExtension_neBot, ?_⟩
  rw [effectiveDomain_negativeSqrtOneSubNormSqExtension, strongConvexOn_iff_convex]
  -- On the effective domain, `toReal` is exactly the finite barrier formula from Chapter 4.
  refine (strongConvexOn_iff_convex.mp ballPenStrongConvexOnClosedBall).congr ?_
  intro x hx
  rw [mem_closedBall_zero_iff] at hx
  simp [negative_sqrt_one_sub_norm_sq_extension_of_norm_le_one hx]

/-- The effective domain of `negative_sqrt_one_sub_norm_sq_extension` is exactly the closed unit
ball. -/
@[simp] theorem mem_effective_domain_negative_sqrt_one_sub_norm_sq_extension {x : E} :
    x ∈ effective_domain (negative_sqrt_one_sub_norm_sq_extension : E → EReal) ↔
      x ∈ Metric.closedBall (0 : E) 1 := by
  -- Reuse the owner-side domain characterization established for the main proof.
  simpa using memEffectiveDomain_negativeSqrtOneSubNormSqExtension_iff (x := x)

/-- Set-level form of `mem_effective_domain_negative_sqrt_one_sub_norm_sq_extension`. -/
theorem effective_domain_negative_sqrt_one_sub_norm_sq_extension :
    effective_domain (negative_sqrt_one_sub_norm_sq_extension : E → EReal) =
      Metric.closedBall (0 : E) 1 := by
  -- The public set-level statement is the corresponding wrapper of the private helper.
  simpa using effectiveDomain_negativeSqrtOneSubNormSqExtension (n := n)

/-- Bridge/view companion to Proposition 5.16: on the closed unit ball, the real-valued barrier
`x ↦ -√(1 - ‖x‖²)` is `1`-strongly convex in mathlib's canonical `StrongConvexOn` form. -/
theorem negative_sqrt_one_sub_norm_sq_extension_strongConvexOn_closedBall :
    StrongConvexOn (Metric.closedBall (0 : E) 1) 1
      (fun x : E ↦ -Real.sqrt (1 - ‖x‖ ^ (2 : ℕ))) := by
  -- The public closed-ball theorem is now a direct wrapper of the owner-side helper.
  simpa using ballPenStrongConvexOnClosedBall (n := n)

end
