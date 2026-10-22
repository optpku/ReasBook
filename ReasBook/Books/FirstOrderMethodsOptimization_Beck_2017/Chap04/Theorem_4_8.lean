/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_8
import FirstOrderMethodsOptimization_Beck_2017.Chap02.FunctionToEReal
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_8
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 4.8 is `source-facing` in the chapter conjugacy calculus. Its ambient notions are the
project owner declarations `IsProperExtendedRealFunction`, `is_convex_function`,
`infimal_convolution`, `conjugate_function`, and the Chapter 2 bridge `Function.toEReal`, so this
file reuses those owners directly rather than restating parallel local copies. -/

-- Proof sketch: fix `y : Module.Dual ℝ E` and apply Fenchel--Rockafellar duality to the pair
-- `h₁` and `g x = h₂ x - y x`. Because `h₂` is finite everywhere, the qualification condition is
-- automatic from properness of `h₁`. Rewriting `g* z` as
-- `conjugate_function h₂.toEReal (y - z)` yields the infimal-convolution formula.
/- Theorem 4.8: if `h₁` is a proper convex extended-real-valued function and `h₂` is a real-valued
convex function, then the Fenchel conjugate of the pointwise sum `h₁ + h₂` is the infimal
convolution of the conjugates `h₁*` and `h₂*`, where the real-valued perturbation enters the
extended-real calculus through the canonical bridge `h₂.toEReal`. The real-valued convexity of
`h₂` is encoded by `ConvexOn ℝ Set.univ h₂`. -/
/-- Helper for Theorem 4.8: negating the infimum of the affine perturbation range recovers the
Fenchel conjugate. -/
private theorem erealSInfRangeSubPairingEqNegConjugate
    (f : E → EReal) (y : Module.Dual ℝ E) :
    sInf (Set.range fun x : E ↦ f x - (y x : EReal)) = -conjugate_function f y := by
  -- Rewrite the affine-perturbation range as the negation of the conjugate-defining range.
  have hrange :
      Set.range (fun x : E ↦ f x - (y x : EReal)) =
        -Set.range (fun x : E ↦ (y x : EReal) - f x) := by
    ext r
    constructor
    · intro hr
      rcases hr with ⟨x, rfl⟩
      rw [Set.mem_neg]
      refine ⟨x, ?_⟩
      have hy_ne_bot : (y x : EReal) ≠ ⊥ := by
        simp
      have hy_ne_top : (y x : EReal) ≠ ⊤ := by
        simp
      have hneg : -(f x - (y x : EReal)) = ((y x : EReal) - f x) := by
        have hraw : -(f x - (y x : EReal)) = -f x + (y x : EReal) := by
          exact EReal.neg_sub (Or.inr hy_ne_bot) (Or.inr hy_ne_top)
        simpa [sub_eq_add_neg, add_comm] using hraw
      simpa using hneg.symm
    · rw [Set.mem_neg]
      intro hr
      rcases hr with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      have hy_ne_bot : (y x : EReal) ≠ ⊥ := by
        simp
      have hy_ne_top : (y x : EReal) ≠ ⊤ := by
        simp
      have hneg : -(f x - (y x : EReal)) = ((y x : EReal) - f x) := by
        have hraw : -(f x - (y x : EReal)) = -f x + (y x : EReal) := by
          exact EReal.neg_sub (Or.inr hy_ne_bot) (Or.inr hy_ne_top)
        simpa [sub_eq_add_neg, add_comm] using hraw
      have hr' : ((y x : EReal) - f x) = -r := by
        simpa using hx
      calc
        f x - (y x : EReal) = -(((y x : EReal) - f x)) := by
              simpa [sub_eq_add_neg, add_comm] using congrArg Neg.neg hneg
        _ = -(-r) := by rw [hr']
        _ = r := by simp
  -- Translate the infimum of the negated range into the negative supremum from the conjugate.
  rw [hrange, ereal_sInf_neg, conjugate_function_apply]

/-- Helper for Theorem 4.8: evaluating the conjugate of `h₁ + h₂.toEReal` at `y` rewrites to the
negated primal infimum for the shifted perturbation `x ↦ h₂ x - y x`. -/
private theorem conjugateFunctionAddEval_eq_negSInfShifted
    (h₁ : E → EReal) (h₂ : E → ℝ) (y : Module.Dual ℝ E) :
    conjugate_function (fun x ↦ h₁ x + h₂.toEReal x) y =
      -sInf (Set.range fun x : E ↦ h₁ x + Function.toEReal (fun z ↦ h₂ z - y z) x) := by
  let f : E → EReal := fun x ↦ h₁ x + h₂.toEReal x
  have hsInf :
      sInf (Set.range fun x : E ↦ f x - (y x : EReal)) = -conjugate_function f y :=
    erealSInfRangeSubPairingEqNegConjugate f y
  have hrange :
      Set.range (fun x : E ↦ f x - (y x : EReal)) =
        Set.range (fun x : E ↦ h₁ x + Function.toEReal (fun z ↦ h₂ z - y z) x) := by
    ext r
    constructor
    · intro hr
      rcases hr with ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      simp [f, Function.toEReal, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    · intro hr
      rcases hr with ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      simp [f, Function.toEReal, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- Normalize the conjugate evaluation into the primal objective used by Fenchel duality.
  have hsInfNeg :
      -sInf (Set.range fun x : E ↦ f x - (y x : EReal)) = conjugate_function f y := by
    simpa using congrArg Neg.neg hsInf
  calc
    conjugate_function (fun x ↦ h₁ x + h₂.toEReal x) y
        = -sInf (Set.range fun x : E ↦ f x - (y x : EReal)) := by
            simpa [f] using hsInfNeg.symm
    _ = -sInf (Set.range fun x : E ↦ h₁ x + Function.toEReal (fun z ↦ h₂ z - y z) x) := by
            rw [hrange]

/-- Helper for Theorem 4.8: the shifted real lift `x ↦ (h₂ x - y x : ℝ)` is proper after the
canonical coercion to `EReal`. -/
private theorem shiftedRealLiftIsProper
    (h₂ : E → ℝ) (y : Module.Dual ℝ E) :
    IsProperExtendedRealFunction (Function.toEReal (fun x ↦ h₂ x - y x)) := by
  -- The shifted perturbation is finite everywhere, so the Chapter 2 owner theorem applies.
  simpa using Function.toEReal_isProper (fun x : E ↦ h₂ x - y x)

/-- Helper for Theorem 4.8: subtracting a linear functional preserves convexity of the real-valued
perturbation before passing through `Function.toEReal`. -/
private theorem shiftedRealLiftIsConvex
    (h₂ : E → ℝ) (hh₂_convex : ConvexOn ℝ Set.univ h₂) (y : Module.Dual ℝ E) :
    is_convex_function (Function.toEReal (fun x ↦ h₂ x - y x)) := by
  -- Combine the convexity of `h₂` with the concavity of the linear functional `y`.
  have hconcave : ConcaveOn ℝ Set.univ (fun x : E ↦ y x) :=
    y.concaveOn convex_univ
  exact Function.toEReal_isConvexFunction (hh₂_convex.sub hconcave)

/-- Helper for Theorem 4.8: the conjugate of the shifted lift at `-z` matches the conjugate of
`h₂.toEReal` at `y - z`. -/
private theorem conjugateFunction_shiftedRealLift
    (h₂ : E → ℝ) (y z : Module.Dual ℝ E) :
    conjugate_function (Function.toEReal (fun x ↦ h₂ x - y x)) (-z) =
      conjugate_function h₂.toEReal (y - z) := by
  have hsInfShifted :
      sInf (Set.range fun x : E ↦ Function.toEReal (fun w ↦ h₂ w - y w) x - (((-z) x : ℝ) : EReal)) =
        -conjugate_function (Function.toEReal (fun x ↦ h₂ x - y x)) (-z) :=
    erealSInfRangeSubPairingEqNegConjugate (Function.toEReal (fun x ↦ h₂ x - y x)) (-z)
  have hpoint :
      ∀ x : E,
        Function.toEReal (fun w ↦ h₂ w - y w) x - (((-z) x : ℝ) : EReal) =
          h₂.toEReal x - (((y - z) x : ℝ) : EReal) := by
    intro x
    change ((((h₂ x - y x) - (-z x) : ℝ)) : EReal) =
      (((h₂ x - (y - z) x : ℝ)) : EReal)
    congr 1
    have hyz : (y - z) x = y x - z x := by
      simp
    rw [hyz]
    ring_nf
  have hrange :
      Set.range
          (fun x : E ↦ Function.toEReal (fun w ↦ h₂ w - y w) x - (((-z) x : ℝ) : EReal)) =
        Set.range (fun x : E ↦ h₂.toEReal x - (((y - z) x : ℝ) : EReal)) := by
    ext r
    constructor
    · intro hr
      rcases hr with ⟨x, rfl⟩
      exact ⟨x, (hpoint x).symm⟩
    · intro hr
      rcases hr with ⟨x, rfl⟩
      exact ⟨x, hpoint x⟩
  have hsInfBase :
      sInf (Set.range fun x : E ↦ h₂.toEReal x - (((y - z) x : ℝ) : EReal)) =
        -conjugate_function h₂.toEReal (y - z) :=
    erealSInfRangeSubPairingEqNegConjugate h₂.toEReal (y - z)
  -- Normalize both conjugates to the same shifted infimum and compare those normal forms.
  have hsInfShiftedNeg :
      -sInf
          (Set.range
            fun x : E ↦ Function.toEReal (fun w ↦ h₂ w - y w) x - (((-z) x : ℝ) : EReal)) =
        conjugate_function (Function.toEReal (fun x ↦ h₂ x - y x)) (-z) := by
    simpa using congrArg Neg.neg hsInfShifted
  have hsInfBaseNeg :
      -sInf (Set.range fun x : E ↦ h₂.toEReal x - (((y - z) x : ℝ) : EReal)) =
        conjugate_function h₂.toEReal (y - z) := by
    simpa using congrArg Neg.neg hsInfBase
  calc
    conjugate_function (Function.toEReal (fun x ↦ h₂ x - y x)) (-z)
        = -sInf
            (Set.range
              fun x : E ↦ Function.toEReal (fun w ↦ h₂ w - y w) x - (((-z) x : ℝ) : EReal)) := by
            simpa using hsInfShiftedNeg.symm
    _ = -sInf (Set.range fun x : E ↦ h₂.toEReal x - (((y - z) x : ℝ) : EReal)) := by
            rw [hrange]
    _ = conjugate_function h₂.toEReal (y - z) := by
            simpa using hsInfBaseNeg

/-- Helper for Theorem 4.8: the shifted real lift has full effective domain because it is finite
everywhere. -/
private theorem shiftedRealLiftEffectiveDomain_eq_univ
    (h₂ : E → ℝ) (y : Module.Dual ℝ E) :
    effective_domain (Function.toEReal (fun x ↦ h₂ x - y x)) = Set.univ := by
  -- Every value of the real-valued perturbation stays finite after the `toEReal` lift.
  ext x
  constructor
  · intro _
    simp
  · intro _
    simpa [effective_domain, Function.toEReal, EReal.coe_sub] using
      (EReal.coe_lt_top (h₂ x - y x))

/-- Helper for Theorem 4.8: the Fenchel qualification is automatic for the shifted lift because
its effective domain is all of `E`. -/
private theorem shiftedRealLiftQualification
    (h₁ : E → EReal) (h₂ : E → ℝ) (y : Module.Dual ℝ E)
    (hh₁_proper : IsProperExtendedRealFunction h₁)
    (hh₁_convex : is_convex_function h₁) :
    (intrinsicInterior ℝ (effective_domain h₁) ∩
      intrinsicInterior ℝ (effective_domain (Function.toEReal (fun x ↦ h₂ x - y x)))).Nonempty := by
  -- Take a relative-interior witness from the proper convex effective domain of `h₁`.
  rcases
      (intrinsicInterior_nonempty
        (effective_domain_convex_of_is_convex_function hh₁_convex)).2
        hh₁_proper.effective_domain_nonempty with
    ⟨x₀, hx₀⟩
  refine ⟨x₀, hx₀, ?_⟩
  rw [shiftedRealLiftEffectiveDomain_eq_univ]
  -- The whole space has nonempty interior, hence nonempty intrinsic interior.
  exact interior_subset_intrinsicInterior (by simpa [interior_univ])

/-- Helper for Theorem 4.8: the Fenchel dual objective for the shifted perturbation is exactly
the negative infimal-convolution integrand. -/
private theorem fenchelDualObjective_shiftedRealLift
    (h₁ : E → EReal) (h₂ : E → ℝ)
    (hh₁_proper : IsProperExtendedRealFunction h₁)
    (y z : Module.Dual ℝ E) :
    fenchel_dual_objective h₁ (Function.toEReal (fun x ↦ h₂ x - y x)) z =
      -(conjugate_function h₁ z + conjugate_function h₂.toEReal (y - z)) := by
  have hh₁_conj_ne_bot : conjugate_function h₁ z ≠ ⊥ :=
    conjugate_function_ne_bot_of_proper h₁ hh₁_proper z
  have hh₂_conj_ne_bot : conjugate_function h₂.toEReal (y - z) ≠ ⊥ :=
    conjugate_function_ne_bot_of_proper h₂.toEReal (Function.toEReal_isProper h₂) (y - z)
  -- Rewrite the owner-level dual objective into the shifted-conjugate normal form.
  calc
    fenchel_dual_objective h₁ (Function.toEReal (fun x ↦ h₂ x - y x)) z
        = -conjugate_function h₁ z -
            conjugate_function (Function.toEReal (fun x ↦ h₂ x - y x)) (-z) := by
            rw [fenchel_dual_objective_apply]
    _ = -conjugate_function h₁ z - conjugate_function h₂.toEReal (y - z) := by
            rw [conjugateFunction_shiftedRealLift]
    _ = -(conjugate_function h₁ z + conjugate_function h₂.toEReal (y - z)) := by
            rw [(EReal.neg_add (.inl hh₁_conj_ne_bot) (.inr hh₂_conj_ne_bot)).symm]

/-- Theorem 4.8: if `h₁` is a proper convex extended-real-valued function and `h₂` is a real-valued
convex function, then the Fenchel conjugate of the pointwise sum `h₁ + h₂` is the infimal
convolution of the conjugates `h₁*` and `h₂*`, where the real-valued perturbation enters the
extended-real calculus through the canonical bridge `h₂.toEReal`. The real-valued convexity of
`h₂` is encoded by `ConvexOn ℝ Set.univ h₂`. -/
theorem conjugate_function_add_eq_infimal_convolution
    (h₁ : E → EReal) (h₂ : E → ℝ) (hh₁_proper : IsProperExtendedRealFunction h₁)
    (hh₁_convex : is_convex_function h₁) (hh₂_convex : ConvexOn ℝ Set.univ h₂) :
    conjugate_function (fun x ↦ h₁ x + h₂.toEReal x) =
      conjugate_function h₁ □ conjugate_function h₂.toEReal := by
  ext y
  let g_y : E → EReal := Function.toEReal (fun x ↦ h₂ x - y x)
  have hg_proper : IsProperExtendedRealFunction g_y := by
    -- The shifted perturbation is finite-valued everywhere.
    simpa [g_y] using shiftedRealLiftIsProper h₂ y
  have hg_convex : is_convex_function g_y := by
    -- Subtracting a linear functional preserves convexity before the `toEReal` lift.
    simpa [g_y] using shiftedRealLiftIsConvex h₂ hh₂_convex y
  have hqual :
      (intrinsicInterior ℝ (effective_domain h₁) ∩
        intrinsicInterior ℝ (effective_domain g_y)).Nonempty := by
    -- The qualification reduces to the nonempty relative interior of `effective_domain h₁`.
    simpa [g_y] using shiftedRealLiftQualification h₁ h₂ y hh₁_proper hh₁_convex
  have hdualRange :
      Set.range (fenchel_dual_objective h₁ g_y) =
        Set.range fun z : Module.Dual ℝ E ↦
          -(conjugate_function h₁ z + conjugate_function h₂.toEReal (y - z)) := by
    -- Normalize each dual objective value into the infimal-convolution integrand.
    ext r
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, by
        simpa [g_y] using (fenchelDualObjective_shiftedRealLift h₁ h₂ hh₁_proper y z).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, by simpa [g_y] using fenchelDualObjective_shiftedRealLift h₁ h₂ hh₁_proper y z⟩
  have hnegIntegrandRange :
      Set.range
          (fun z : Module.Dual ℝ E ↦
            -(conjugate_function h₁ z + conjugate_function h₂.toEReal (y - z))) =
        -Set.range
          (fun z : Module.Dual ℝ E ↦
            conjugate_function h₁ z + conjugate_function h₂.toEReal (y - z)) := by
    -- The negated dual integrands are exactly the pointwise negation of the positive range.
    ext r
    constructor
    · rintro ⟨z, rfl⟩
      rw [Set.mem_neg]
      simpa using (Set.mem_range_self z)
    · rw [Set.mem_neg]
      rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      simpa using congrArg Neg.neg hz
  -- Evaluate the conjugate pointwise and then invoke Fenchel duality for the shifted perturbation.
  calc
    conjugate_function (fun x ↦ h₁ x + h₂.toEReal x) y
        = -sInf (Set.range fun x : E ↦ h₁ x + g_y x) := by
            simpa [g_y] using conjugateFunctionAddEval_eq_negSInfShifted h₁ h₂ y
    _ = -fenchel_dual_problem_value h₁ g_y := by
            rw [fenchel_duality_value_eq h₁ g_y hh₁_proper hg_proper hh₁_convex hg_convex hqual]
    _ = -sSup (Set.range (fenchel_dual_objective h₁ g_y)) := by
            rw [fenchel_dual_problem_value_eq_sSup]
    _ = -sSup
          (Set.range fun z : Module.Dual ℝ E ↦
            -(conjugate_function h₁ z + conjugate_function h₂.toEReal (y - z))) := by
            rw [hdualRange]
    _ = -sSup
          (-Set.range
            (fun z : Module.Dual ℝ E ↦
              conjugate_function h₁ z + conjugate_function h₂.toEReal (y - z))) := by
            rw [hnegIntegrandRange]
    _ = sInf
          (Set.range fun z : Module.Dual ℝ E ↦
            conjugate_function h₁ z + conjugate_function h₂.toEReal (y - z)) := by
            simpa using
              (ereal_sInf_neg
                (-Set.range
                  (fun z : Module.Dual ℝ E ↦
                    conjugate_function h₁ z + conjugate_function h₂.toEReal (y - z)))).symm
    _ = (conjugate_function h₁ □ conjugate_function h₂.toEReal) y := by
            rw [infimal_convolution_apply, sInf_range]

end
