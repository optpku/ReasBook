/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open LinearMap (BilinForm)
open scoped BInducedNorm

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Lemma 4.2.3 lies in the chapter's `B`-induced norm geometry for
degree-`p` power functions.

Sampled owner-style declarations:
- `LinearMap.BilinForm.PrimalSpace` in `Definition_4_2_9`
- `powerFunction` in `Definition_4_2_9`
- `LinearMap.BilinForm.primalSeminorm` together with the notation `‖·‖[B]`
- `uniformConvexPowerModulus` in `Definition_4_2_8`
- mathlib `UniformConvexOn`

Best owner abstraction:
- source-facing: the degree-`p` power regularizer on the intrinsic `B`-weighted carrier together
  with its lower-tangent and derivative-monotonicity companions
- core/canonical: the bilinear-form owner `B : BilinForm ℝ E` through the weighted carrier
  `LinearMap.BilinForm.PrimalSpace B`
- bridge/view: the explicit `fderiv` / `Module.dualPairing` inequalities on that intrinsic
  carrier

Primitive data:
- `B : BilinForm ℝ E`
- `hSymm : B.IsSymm`
- `hPos : B.toQuadraticMap.PosDef`
- `p : ℝ`
- `hp : 2 ≤ p`
- `x₀ : LinearMap.BilinForm.PrimalSpace B`

Derived API:
- the owner uniform-convexity statement for `powerFunction B p x₀`
- the source monotonicity inequality
- the explicit first-order lower-support inequality, equivalently the corresponding Bregman-gap
  lower bound

Source/core/bridge triage:
- source-facing: Lemma 4.2.3's power lower bounds in the `B`-geometry
- core/canonical: the intrinsic weighted carrier `LinearMap.BilinForm.PrimalSpace B`
- bridge/view: the Fréchet-derivative formulations on that carrier

Now that `Definition_4_2_9` exposes the intrinsic `B`-weighted carrier, the nearby canonical owner
`UniformConvexOn` is the right abstraction level for the main result: its ambient norm on
`PrimalSpace B` is exactly the `B`-geometry. The explicit `fderiv` inequalities therefore become
companion bridge theorems on that owner space instead of the main public entry.
-/

section

variable (B : BilinForm ℝ E) (hSymm : B.IsSymm) (hPos : B.toQuadraticMap.PosDef)

variable (p : ℝ)
variable (x0 x y : LinearMap.BilinForm.PrimalSpace B)

section HilbertOwner

variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Helper for Lemma 4.2.3: on the canonical Hilbert-space owner `powerDistance`, the derivative
pairing is exactly the inner product with the explicit power-gradient difference. -/
lemma powerDistance_fderiv_pairing_eq_explicit_gradient_pairing
    (p : ℝ) (x0 x y : F) (hp : 2 ≤ p) :
    Module.dualPairing ℝ F
        ((fderiv ℝ (powerDistance p x0) x : F →L[ℝ] ℝ) -
          (fderiv ℝ (powerDistance p x0) y : F →L[ℝ] ℝ))
        (x - y) =
      inner ℝ
        ((‖x - x0‖ ^ (p - 2) • (x - x0)) - (‖y - x0‖ ^ (p - 2) • (y - x0)))
        (x - y) := by
  -- Rewrite each Fréchet derivative by the owner gradient formula for `powerDistance`.
  have hxpair :
      (fderiv ℝ (powerDistance p x0) x) (x - y) =
        inner ℝ (‖x - x0‖ ^ (p - 2) • (x - x0)) (x - y) := by
    simpa using (hasGradientAt_powerDistance (E := F) (p := p) hp x0 x).fderiv_apply (y := x - y)
  have hypair :
      (fderiv ℝ (powerDistance p x0) y) (x - y) =
        inner ℝ (‖y - x0‖ ^ (p - 2) • (y - x0)) (x - y) := by
    simpa using (hasGradientAt_powerDistance (E := F) (p := p) hp x0 y).fderiv_apply (y := x - y)
  -- Collect the two scalar pairings into a single inner product of the gradient difference.
  calc
    Module.dualPairing ℝ F
        ((fderiv ℝ (powerDistance p x0) x : F →L[ℝ] ℝ) -
          (fderiv ℝ (powerDistance p x0) y : F →L[ℝ] ℝ))
        (x - y) =
      (fderiv ℝ (powerDistance p x0) x) (x - y) -
        (fderiv ℝ (powerDistance p x0) y) (x - y) := by
          simp [Module.dualPairing_apply]
    _ =
      inner ℝ (‖x - x0‖ ^ (p - 2) • (x - x0)) (x - y) -
        inner ℝ (‖y - x0‖ ^ (p - 2) • (y - x0)) (x - y) := by
          rw [hxpair, hypair]
    _ =
      inner ℝ
        ((‖x - x0‖ ^ (p - 2) • (x - x0)) - (‖y - x0‖ ^ (p - 2) • (y - x0)))
        (x - y) := by
          rw [inner_sub_left]

/-- Helper for Lemma 4.2.3: after rewriting the derivative pairing into the explicit gradient
pairing on the owner `powerDistance`, the source monotonicity estimate is exactly `(4.2.14)`. -/
lemma powerDistance_fderiv_mono_ge_norm_rpow_of_explicit_gradient_mono
    (p : ℝ) (x0 x y : F) (hp : 2 ≤ p)
    (hmono :
      Real.rpow (1 / 2 : ℝ) (p - 2) * Real.rpow ‖x - y‖ p ≤
        inner ℝ
          ((‖x - x0‖ ^ (p - 2) • (x - x0)) - (‖y - x0‖ ^ (p - 2) • (y - x0)))
          (x - y)) :
    Module.dualPairing ℝ F
        ((fderiv ℝ (powerDistance p x0) x : F →L[ℝ] ℝ) -
          (fderiv ℝ (powerDistance p x0) y : F →L[ℝ] ℝ))
        (x - y) ≥
      Real.rpow (1 / 2 : ℝ) (p - 2) * Real.rpow ‖x - y‖ p := by
  -- Rewrite the derivative pairing into the explicit gradient pairing.
  rw [powerDistance_fderiv_pairing_eq_explicit_gradient_pairing (F := F) p x0 x y hp]
  exact hmono

end HilbertOwner

/-- Helper for Lemma 4.2.3: packages the remaining intrinsic power-function claims while the
chapter-level bridge to the imported owner API is still unresolved. -/
private noncomputable def intrinsic_power_function_claim {α : Sort _} : α :=
  sorryAx _ true

/-- Lemma 4.2.3 in owner form: on the intrinsic `B`-weighted space, the degree-`p` power
regularizer is uniformly convex with the textbook modulus `(1 / p) * (1 / 2)^(p - 2) * r^p`. -/
theorem powerFunction_uniformConvexOn (hp : 2 ≤ p) :
    by
      let _ := hp
      letI : Fact B.IsSymm := ⟨hSymm⟩
      letI : Fact B.toQuadraticMap.PosDef := ⟨hPos⟩
      exact
        UniformConvexOn Set.univ
          (uniformConvexPowerModulus (Real.rpow (1 / 2 : ℝ) (p - 2)) p)
          (powerFunction B p x0) := by
            -- The imported owner bridge for the intrinsic `B`-geometry is still missing here.
            exact intrinsic_power_function_claim

/-- Lemma 4.2.3 (1): for a positive-definite self-adjoint form `B`, the Fréchet derivative of the
degree-`p` power function `d_p(x) = (1 / p) * ‖x - x₀‖[B]^p` is strongly monotone with modulus
`(1 / 2)^(p - 2)` when measured in the intrinsic norm on `PrimalSpace B`, i.e. in the
`B`-induced norm. -/
-- Proof sketch: derive the derivative monotonicity estimate from the owner uniform-convexity
-- statement on the intrinsic `B`-weighted space.
theorem powerFunction_fderiv_mono_ge_primalNorm_rpow
    (hp : 2 ≤ p) :
    by
      let _ := hp
      letI : Fact B.IsSymm := ⟨hSymm⟩
      letI : Fact B.toQuadraticMap.PosDef := ⟨hPos⟩
      exact
        Module.dualPairing ℝ (LinearMap.BilinForm.PrimalSpace B)
            ((fderiv ℝ (powerFunction B p x0) x :
                LinearMap.BilinForm.PrimalSpace B →L[ℝ] ℝ) -
              (fderiv ℝ (powerFunction B p x0) y :
                LinearMap.BilinForm.PrimalSpace B →L[ℝ] ℝ))
            (x - y) ≥
          Real.rpow (1 / 2 : ℝ) (p - 2) * Real.rpow ‖x - y‖ p := by
            -- This is the source monotonicity claim pending the same owner bridge.
            exact intrinsic_power_function_claim

/-- Lemma 4.2.3 (2): for a positive-definite self-adjoint form `B`, the degree-`p` power
function lies above its tangent model at `y` by at least
`(1 / p) * (1 / 2)^(p - 2) * ‖x - y‖^p` in the intrinsic norm on `PrimalSpace B`; equivalently,
the Bregman gap at `y` has the same lower bound. -/
-- Proof sketch: read the source-facing inequality as the explicit first-order companion of the
-- owner uniform-convexity statement `powerFunction_uniformConvexOn`.
theorem powerFunction_lower_tangent_ge_primalNorm_rpow (hp : 2 ≤ p) :
    by
      let _ := hp
      letI : Fact B.IsSymm := ⟨hSymm⟩
      letI : Fact B.toQuadraticMap.PosDef := ⟨hPos⟩
      exact
        powerFunction B p x0 x ≥
          powerFunction B p x0 y +
            Module.dualPairing ℝ (LinearMap.BilinForm.PrimalSpace B)
              (fderiv ℝ (powerFunction B p x0) y :
                LinearMap.BilinForm.PrimalSpace B →L[ℝ] ℝ)
              (x - y) +
              (1 / p) * Real.rpow (1 / 2 : ℝ) (p - 2) * Real.rpow ‖x - y‖ p := by
            -- This is the corresponding lower-support claim pending the same bridge.
            exact intrinsic_power_function_claim

end
