/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1
import Mathlib.Topology.Instances.EReal.Lemmas

-- Declarations for this support owner are maintained manually.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

recall effective_domain
recall conjugate_function

/- This support owner file exposes the continuous-dual view of Chapter 4's Fenchel conjugate.
The bridge is a thin pullback of `conjugate_function` along the canonical coercion
`StrongDual ℝ E → Module.Dual ℝ E`, so downstream files can work on the normed dual without
introducing a second root owner for conjugation. -/

/-- The Fenchel conjugate on the continuous dual, obtained by restricting the Chapter 4 owner
`conjugate_function` along the canonical coercion `StrongDual ℝ E → Module.Dual ℝ E`. -/
noncomputable abbrev conjugate_function_strongDual (f : E → EReal) : StrongDual ℝ E → EReal :=
  fun y ↦ conjugate_function f y

/-- Evaluating the continuous-dual Fenchel conjugate is the same as evaluating the Chapter 4 owner
at the underlying algebraic functional. -/
@[simp] theorem conjugate_function_strongDual_apply (f : E → EReal) (y : StrongDual ℝ E) :
    conjugate_function_strongDual f y = conjugate_function f y :=
  rfl

/-- Membership in the finite-valued domain of the continuous-dual Fenchel conjugate is exactly the
expected pointwise finiteness condition. -/
@[simp] theorem mem_effective_domain_conjugate_function_strongDual
    {f : E → EReal} {y : StrongDual ℝ E} :
    y ∈ effective_domain (conjugate_function_strongDual f) ↔
      conjugate_function_strongDual f y < ⊤ :=
  Iff.rfl

/-- The continuous-dual Fenchel conjugate is lower semicontinuous and convex. This is the
canonical `StrongDual ℝ E` analogue of Chapter 4's conjugate closed/convex owner theorem, so
downstream Chapter 5 files should reuse it instead of reproving the same affine-supremum argument
locally. -/
theorem conjugateFunctionStrongDual_closedConvex (f : E → EReal) :
    LowerSemicontinuous (conjugate_function_strongDual f) ∧
      is_convex_function (conjugate_function_strongDual f) := by
  let evalSlice : E → StrongDual ℝ E → EReal := fun x y ↦ (y x : EReal)
  have isConvexFunctionERealConst :
      ∀ c : EReal, is_convex_function (fun _ : StrongDual ℝ E ↦ c) := by
    intro c
    by_cases hbot : c = ⊥
    · rw [hbot, is_convex_function_iff_convex_real_epigraph]
      have hEpigraph :
          {p : StrongDual ℝ E × ℝ | (⊥ : EReal) ≤ (p.2 : EReal)} = Set.univ := by
        ext p
        simp
      rw [hEpigraph]
      exact (convex_univ : Convex ℝ (Set.univ : Set (StrongDual ℝ E × ℝ)))
    by_cases htop : c = ⊤
    · rw [htop, is_convex_function_iff_convex_real_epigraph]
      have hEpigraph :
          {p : StrongDual ℝ E × ℝ | (⊤ : EReal) ≤ (p.2 : EReal)} =
            (∅ : Set (StrongDual ℝ E × ℝ)) := by
        ext p
        simp
      rw [hEpigraph]
      exact (convex_empty : Convex ℝ (∅ : Set (StrongDual ℝ E × ℝ)))
    have hfinite : c = (((c.toReal : ℝ)) : EReal) := by
      symm
      exact EReal.coe_toReal htop hbot
    rw [hfinite, is_convex_function_iff_convex_real_epigraph]
    have hEpigraph :
        {p : StrongDual ℝ E × ℝ | (((c.toReal : ℝ) : EReal)) ≤ (p.2 : EReal)} =
          Set.univ ×ˢ Set.Ici c.toReal := by
      ext p
      simp
    rw [hEpigraph]
    exact convex_univ.prod (convex_Ici _)
  have affineEvalSubRealClosedConvex :
      ∀ x : E, ∀ c : ℝ,
        LowerSemicontinuous (fun y : StrongDual ℝ E ↦ (((y x - c : ℝ) : EReal))) ∧
          is_convex_function (fun y : StrongDual ℝ E ↦ (((y x - c : ℝ) : EReal))) := by
    intro x c
    constructor
    · have hEvalCont : Continuous (fun y : StrongDual ℝ E ↦ y x) := by
        simpa using (ContinuousLinearMap.apply ℝ ℝ x).continuous
      have hCont : Continuous (fun y : StrongDual ℝ E ↦ (((y x - c : ℝ) : EReal))) := by
        exact (continuous_coe_real_ereal.comp (hEvalCont.sub continuous_const))
      exact hCont.lowerSemicontinuous
    · have hConst :
          is_convex_function (fun _ : StrongDual ℝ E ↦ (((-c : ℝ) : EReal))) :=
        isConvexFunctionERealConst (((-c : ℝ) : EReal))
      have hSum :
          is_convex_function
            ((fun y : StrongDual ℝ E ↦ (((y x : ℝ) : EReal))) +
              fun _ : StrongDual ℝ E ↦ (((-c : ℝ) : EReal))) := by
        exact
          is_convex_function_pointwise_add
            (by
              rw [is_convex_function_iff_convex_real_epigraph]
              simpa [Set.setOf_and, Set.mem_univ] using
                (show Convex ℝ {p : StrongDual ℝ E × ℝ | p.1 ∈ Set.univ ∧ p.1 x ≤ p.2} from
                  (LinearMap.convexOn ((ContinuousLinearMap.apply ℝ ℝ x).toLinearMap)
                    convex_univ).convex_epigraph))
            hConst
            (fun y ↦ by simp)
            (fun y ↦ by simp)
      simpa [Pi.add_apply, sub_eq_add_neg] using hSum
  have affineEvalMinusValueClosedConvex :
      ∀ x : E,
        LowerSemicontinuous (fun y : StrongDual ℝ E ↦ (evalSlice x y - f x)) ∧
          is_convex_function (fun y : StrongDual ℝ E ↦ (evalSlice x y - f x)) := by
    intro x
    by_cases hbot : f x = ⊥
    · simpa [evalSlice, hbot] using
        (show LowerSemicontinuous (fun _ : StrongDual ℝ E ↦ (⊤ : EReal)) ∧
            is_convex_function (fun _ : StrongDual ℝ E ↦ (⊤ : EReal)) from
          ⟨lowerSemicontinuous_const, isConvexFunctionERealConst ⊤⟩)
    by_cases htop : f x = ⊤
    · simpa [evalSlice, htop] using
        (show LowerSemicontinuous (fun _ : StrongDual ℝ E ↦ (⊥ : EReal)) ∧
            is_convex_function (fun _ : StrongDual ℝ E ↦ (⊥ : EReal)) from
          ⟨lowerSemicontinuous_const, isConvexFunctionERealConst ⊥⟩)
    have hfinite : f x = ((((f x).toReal : ℝ)) : EReal) := by
      symm
      exact EReal.coe_toReal htop hbot
    rw [hfinite]
    simpa [evalSlice, EReal.coe_sub] using affineEvalSubRealClosedConvex x (f x).toReal
  have hrepr :
      conjugate_function_strongDual f = fun y ↦ ⨆ x : E, (evalSlice x y - f x) := by
    funext y
    rw [conjugate_function_strongDual_apply, conjugate_function_apply, sSup_range]
    simp [evalSlice]
  rw [hrepr]
  constructor
  · exact lowerSemicontinuous_iSup fun x ↦ (affineEvalMinusValueClosedConvex x).1
  · exact is_convex_function_iSup fun x ↦ (affineEvalMinusValueClosedConvex x).2

end
