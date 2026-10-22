/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Module LinearMap

universe u

/- Definition 4.3.4 lies in the bilinear-form / induced-seminorm / finite-dimensional duality
domain.

Sampled owner-style declarations:
- project `Seminorm.IsNorm`
- project `Seminorm.dualNorm`
- project `Seminorm.primalDualOperatorNorm`
- `QuadraticMap.PosDef`
- `QuadraticMap.associated`
- `QuadraticMap.associated_eq_self_apply`
- `LinearMap.BilinForm.toDual`
- `LinearMap.BilinForm.apply_toDual_symm_apply`

Best owner abstraction:
- source-facing: the dual norm induced by the positive-definite quadratic data of a bilinear form
- core/canonical: the induced seminorm owner `primalSeminorm B : Seminorm ℝ E`, defined from
  `B.toQuadraticMap` and its canonical associated symmetric bilinear form
- bridge/view: the finite-dimensional dual equivalence `B.toDual`

Primitive data:
- `B : BilinForm ℝ E`
- `hPos : B.toQuadraticMap.PosDef`

Derived API:
- the pointwise formula for the induced seminorm
- in finite dimension, the derived source-facing dual norm on `E⋆`
- positive-definite nondegeneracy of `B`
- the canonical preimage map `dualPreimage hPos : E⋆ → E`, i.e. the source-facing `B⁻¹`
  applied to a covector
- under symmetry, the `B.toDual` bridge from the dual norm to the textbook inverse-pairing
  formula

The primal and support-function owners depend only on the positive-definite quadratic data
`B.toQuadraticMap`; symmetry is retained only for the later `B.toDual` bridge theorem, where the
inverse-pairing formula genuinely needs a symmetric representative. The primal owner is exposed as
a reusable `Seminorm` rather than a parallel function-valued wrapper.
-/

namespace LinearMap.BilinForm

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- Definition 4.3.4 in owner form: the positive-definite quadratic data of `B` induce the
canonical seminorm `x ↦ ⟪Bx, x⟫^(1/2)`. -/
def primalSeminorm (B : LinearMap.BilinForm ℝ E) (hPos : B.toQuadraticMap.PosDef) :
    Seminorm ℝ E :=
  Seminorm.of (fun x ↦ Real.sqrt (B.toQuadraticMap x))
    (fun x y ↦ by
      let A : LinearMap.BilinForm ℝ E := B.toQuadraticMap.associated
      have hA_symm : A.IsSymm := by
        exact ⟨QuadraticMap.associated_isSymm ℝ B.toQuadraticMap⟩
      have hA_linear : LinearMap.IsSymm A := LinearMap.BilinForm.isSymm_iff.1 hA_symm
      have hdiag : ∀ z : E, A z z = B.toQuadraticMap z := fun z ↦ by
        simpa [A] using QuadraticMap.associated_eq_self_apply ℝ B.toQuadraticMap z
      have hs : ∀ z : E, 0 ≤ A z z := fun z ↦ by
        rw [hdiag z]
        exact hPos.nonneg z
      have hxy_sq : (A x y) ^ 2 ≤ (Real.sqrt (A x x) * Real.sqrt (A y y)) ^ 2 := by
        have hbase : (A x y) ^ 2 ≤ (A x x) * (A y y) := A.apply_sq_le_of_symm hs hA_linear x y
        nlinarith [hbase, Real.sq_sqrt (hs x), Real.sq_sqrt (hs y)]
      have hxy : A x y ≤ Real.sqrt (A x x) * Real.sqrt (A y y) := by
        exact le_of_sq_le_sq hxy_sq (by positivity)
      have hyx : A y x ≤ Real.sqrt (A x x) * Real.sqrt (A y y) := by
        calc
          A y x = A x y := hA_symm.eq _ _
          _ ≤ Real.sqrt (A x x) * Real.sqrt (A y y) := hxy
      have hsum : A x y + A y x ≤ 2 * (Real.sqrt (A x x) * Real.sqrt (A y y)) := by
        nlinarith [hxy, hyx]
      have hsq :
          A (x + y) (x + y) ≤
            (Real.sqrt (A x x) + Real.sqrt (A y y)) *
              (Real.sqrt (A x x) + Real.sqrt (A y y)) := by
        calc
          A (x + y) (x + y) = A x x + (A x y + A y x) + A y y := by
            simp [map_add, add_left_comm, add_comm]
          _ ≤ A x x + 2 * (Real.sqrt (A x x) * Real.sqrt (A y y)) + A y y := by
            gcongr
          _ = (Real.sqrt (A x x) + Real.sqrt (A y y)) *
                (Real.sqrt (A x x) + Real.sqrt (A y y)) := by
            nlinarith [Real.sq_sqrt (hs x), Real.sq_sqrt (hs y)]
      have htri :
          Real.sqrt (A (x + y) (x + y)) ≤ Real.sqrt (A x x) + Real.sqrt (A y y) := by
        apply nonneg_le_nonneg_of_sq_le_sq
        · exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        · nlinarith [hsq, Real.sq_sqrt (hs (x + y))]
      simpa only [hdiag (x + y), hdiag x, hdiag y] using htri)
    (fun a x ↦ by
      by_cases ha : a = 0
      · simp [ha]
      have hsx : 0 ≤ B.toQuadraticMap x := hPos.nonneg x
      have hsax : 0 ≤ B.toQuadraticMap (a • x) := hPos.nonneg (a • x)
      refine (Real.sqrt_eq_iff_eq_sq hsax (by positivity)).2 ?_
      have habs : a * a = ‖a‖ * ‖a‖ := by
        calc
          a * a = a ^ 2 := by ring
          _ = ‖a‖ ^ 2 := (sq_abs a).symm
          _ = ‖a‖ * ‖a‖ := by ring
      have hsqrt :
          Real.sqrt (B.toQuadraticMap x) * Real.sqrt (B.toQuadraticMap x) = B.toQuadraticMap x := by
        simpa [sq] using Real.sq_sqrt hsx
      have hsmul :
          B.toQuadraticMap (a • x) = (a * a) * B.toQuadraticMap x := by
        simp [BilinMap.toQuadraticMap_apply, smul_eq_mul, mul_assoc]
      calc
        B.toQuadraticMap (a • x) = (a * a) * B.toQuadraticMap x := hsmul
        _ = (‖a‖ * ‖a‖) * B.toQuadraticMap x := by rw [habs]
        _ = ‖a‖ * ‖a‖ * (Real.sqrt (B.toQuadraticMap x) * Real.sqrt (B.toQuadraticMap x)) := by
          rw [hsqrt]
        _ = ‖a‖ * Real.sqrt (B.toQuadraticMap x) * (‖a‖ * Real.sqrt (B.toQuadraticMap x)) := by
          ring
        _ = ‖a‖ * (fun y ↦ Real.sqrt (B.toQuadraticMap y)) x *
              (‖a‖ * (fun y ↦ Real.sqrt (B.toQuadraticMap y)) x) := by
          rfl
        _ = (‖a‖ * (fun y ↦ Real.sqrt (B.toQuadraticMap y)) x) ^ 2 := by
          ring)

namespace BInducedNorm

/- Source-facing Lean notation for the primal norm induced by the positive-definite quadratic data
of `B`. -/
scoped notation:max "‖" x "‖[" B " | " hPos "]" =>
  LinearMap.BilinForm.primalSeminorm B hPos x

/- Instance-driven shorthand for the primal norm when positive-definiteness is already available
as a local `Fact` instance. -/
scoped notation:max "‖" x "‖[" B "]" =>
  LinearMap.BilinForm.primalSeminorm B Fact.out x

end BInducedNorm

open scoped BInducedNorm

/-- Evaluating `primalSeminorm B` recovers the formula `√(⟪Bx, x⟫)`. -/
@[simp] theorem primalSeminorm_apply (B : LinearMap.BilinForm ℝ E)
    (hPos : B.toQuadraticMap.PosDef) (x : E) :
    ‖x‖[B | hPos] = Real.sqrt (B x x) := by
  rfl

/-- The positive-definite bilinear-form-induced seminorm is separated. -/
instance primalSeminorm_isNorm (B : LinearMap.BilinForm ℝ E) (hPos : B.toQuadraticMap.PosDef) :
    Seminorm.IsNorm (primalSeminorm B hPos) where
  eq_zero_of_map_eq_zero {x} hx := by
    have hsx : 0 ≤ B x x := by
      simpa [BilinMap.toQuadraticMap_apply] using hPos.nonneg x
    have hxx : B x x = 0 := by
      exact (Real.sqrt_eq_zero hsx).mp (by simpa [primalSeminorm_apply] using hx)
    exact hPos.anisotropic x hxx

/-- A bilinear form whose associated quadratic map is positive definite is nondegenerate. -/
theorem nondegenerate_of_posDef (B : LinearMap.BilinForm ℝ E) (hB : B.toQuadraticMap.PosDef) :
    B.Nondegenerate := by
  let B' : LinearMap.BilinForm ℝ E := B.flip
  refine ⟨separatingLeft_of_anisotropic hB.anisotropic, ?_⟩
  intro x hx
  have hflip : B'.toQuadraticMap.Anisotropic := by
    intro y hy
    apply hB.anisotropic y
    simpa [BilinMap.toQuadraticMap_apply] using hy
  exact separatingLeft_of_anisotropic hflip x hx

section

/-- Definition 4.3.4: in finite dimension, the dual norm induced by the positive-definite
quadratic data of `B` is the support function of the primal `B`-unit ball. The finite-dimensional
hypothesis is the source-facing owner layer guaranteeing this support value is an honest real
supremum. -/
def dualNorm [FiniteDimensional ℝ E] (B : LinearMap.BilinForm ℝ E)
    (hPos : B.toQuadraticMap.PosDef) :
    Dual ℝ E → ℝ :=
  fun g ↦ sSup ((fun x : E ↦ g x) '' {x | ‖x‖[B | hPos] ≤ 1})

namespace BInducedNorm

/- Source-facing Lean notation for the bilinear-form dual norm, written so it applies both to
linear dual vectors and to continuous dual vectors via the canonical coercion to `Module.Dual`. -/
scoped notation:max "‖" g "‖*[" B " | " hPos "]" =>
  LinearMap.BilinForm.dualNorm B hPos ((g : _ →ₗ[ℝ] ℝ))

/- Instance-driven shorthand for the bilinear-form dual norm when positive-definiteness is already
available as a local `Fact` instance. -/
scoped notation:max "‖" g "‖[" B ",*]" =>
  LinearMap.BilinForm.dualNorm B Fact.out ((g : _ →ₗ[ℝ] ℝ))

end BInducedNorm

/-- Expanding `dualNorm B` gives the support-function formula over the primal `B`-unit ball. -/
theorem dualNorm_eq_sSup_primalUnitBall [FiniteDimensional ℝ E]
    (B : LinearMap.BilinForm ℝ E) (hPos : B.toQuadraticMap.PosDef) (g : Dual ℝ E) :
    ‖g‖*[B | hPos] = sSup ((fun x : E ↦ g x) '' {x | ‖x‖[B | hPos] ≤ 1}) := rfl

section

variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- On a finite-dimensional real inner-product space, the Chapter 2 dual norm of the primal
seminorm induced by `B` agrees with the Chapter 4 bilinear-form dual norm after passing to the
canonical dual vector `InnerProductSpace.toDual ℝ F x`. -/
theorem seminormDualNorm_eq_dualNorm_toDual [FiniteDimensional ℝ F]
    (B : LinearMap.BilinForm ℝ F) (hPos : B.toQuadraticMap.PosDef) (x : F) :
    Seminorm.dualNorm (B.primalSeminorm hPos) x =
      B.dualNorm hPos (InnerProductSpace.toDual ℝ F x).toLinearMap := by
  rw [Seminorm.dualNorm_apply, dualNorm_eq_sSup_primalUnitBall]
  simp [InnerProductSpace.toDual_apply_apply]

end

/-- The vector `B⁻¹ g`, characterized by the pairing identity `B (B.dualPreimage hPos g) x = g x`.
This is the preimage of `g` under the finite-dimensional equivalence `B.toDual` supplied by
positive-definiteness. -/
abbrev dualPreimage [FiniteDimensional ℝ E] (B : LinearMap.BilinForm ℝ E)
    (hPos : B.toQuadraticMap.PosDef)
    (g : Dual ℝ E) : E :=
  (B.toDual (B.nondegenerate_of_posDef hPos)).symm g

/-- The canonical preimage `B.dualPreimage hPos g` evaluates against `B` to recover `g`. -/
@[simp] theorem dualPreimage_apply [FiniteDimensional ℝ E] (B : LinearMap.BilinForm ℝ E)
    (hPos : B.toQuadraticMap.PosDef) (g : Dual ℝ E) (x : E) :
    B (B.dualPreimage hPos g) x = g x := by
  rw [dualPreimage]
  exact apply_toDual_symm_apply g x

/-- Helper for Definition 4.3.4: the canonical dual preimage pairs with itself through `B` to
recover the scalar `g (B.dualPreimage hPos g)`. -/
private theorem dualPreimage_self_pairing [FiniteDimensional ℝ E]
    (B : LinearMap.BilinForm ℝ E) (hPos : B.toQuadraticMap.PosDef) (g : Dual ℝ E) :
    g (B.dualPreimage hPos g) = B (B.dualPreimage hPos g) (B.dualPreimage hPos g) := by
  -- Evaluate the defining `B.toDual` inverse-pairing identity at the dual preimage itself.
  simpa using
    (B.dualPreimage_apply hPos g (B.dualPreimage hPos g)).symm

/-- Helper for Definition 4.3.4: belonging to the primal `B`-unit ball bounds the quadratic
self-pairing by `1`. -/
private theorem self_apply_le_one_of_primalSeminorm_le_one [FiniteDimensional ℝ E]
    (B : LinearMap.BilinForm ℝ E) (hPos : B.toQuadraticMap.PosDef) {x : E}
    (hx : B.primalSeminorm hPos x ≤ 1) :
    B x x ≤ 1 := by
  -- Square the primal norm inequality after rewriting it as the explicit `√(B x x)` formula.
  have hx_sqrt : Real.sqrt (B x x) ≤ 1 := by
    simpa [B.primalSeminorm_apply] using hx
  have hx_nonneg : 0 ≤ B x x := hPos.nonneg x
  have hsq : (Real.sqrt (B x x)) ^ 2 ≤ (1 : ℝ) ^ 2 := by
    nlinarith [hx_sqrt, Real.sqrt_nonneg (B x x)]
  simpa [Real.sq_sqrt hx_nonneg] using hsq

/-- Helper for Definition 4.3.4: every point of the primal `B`-unit ball evaluates under `g`
below the candidate support value coming from `B.dualPreimage hPos g`. -/
private theorem dual_eval_le_sqrt_dualPreimage_self_of_primalSeminorm_le_one
    [FiniteDimensional ℝ E] (B : LinearMap.BilinForm ℝ E) (hSymm : B.IsSymm)
    (hPos : B.toQuadraticMap.PosDef) (g : Dual ℝ E) {x : E}
    (hx : B.primalSeminorm hPos x ≤ 1) :
    g x ≤ Real.sqrt (g (B.dualPreimage hPos g)) := by
  let z := B.dualPreimage hPos g
  let hLinearSymm : LinearMap.IsSymm B := LinearMap.BilinForm.isSymm_iff.1 hSymm
  have hz_nonneg : 0 ≤ g z := by
    rw [dualPreimage_self_pairing]
    exact hPos.nonneg z
  have hx_self : B x x ≤ 1 := self_apply_le_one_of_primalSeminorm_le_one B hPos hx
  have hsq : (g x) ^ 2 ≤ g z := by
    -- Apply bilinear Cauchy-Schwarz and then use the unit-ball bound `B x x ≤ 1`.
    have hbase : (B z x) ^ 2 ≤ (B z z) * (B x x) :=
      B.apply_sq_le_of_symm hPos.nonneg hLinearSymm z x
    calc
      (g x) ^ 2 = (B z x) ^ 2 := by simp [z]
      _ ≤ (B z z) * (B x x) := hbase
      _ ≤ (B z z) * 1 := by
        exact mul_le_mul_of_nonneg_left hx_self (hPos.nonneg z)
      _ = g z := by
        rw [mul_one]
        simpa [z] using (B.dualPreimage_apply hPos g z)
  -- Compare squares against `(√(g z))² = g z`.
  have hsq' : (g x) ^ 2 ≤ (Real.sqrt (g z)) ^ 2 := by
    simpa [Real.sq_sqrt hz_nonneg] using hsq
  exact le_of_sq_le_sq hsq' (Real.sqrt_nonneg _)

/-- Helper for Definition 4.3.4: normalizing `B.dualPreimage hPos g` by the support value places
it on the primal `B`-unit sphere and realizes equality in the support bound. -/
private theorem normalized_dualPreimage_attains_support [FiniteDimensional ℝ E]
    (B : LinearMap.BilinForm ℝ E) (hPos : B.toQuadraticMap.PosDef) (g : Dual ℝ E)
    (hz : 0 < g (B.dualPreimage hPos g)) :
    let z := B.dualPreimage hPos g
    let w := (Real.sqrt (g z))⁻¹ • z
    B.primalSeminorm hPos w ≤ 1 ∧ g w = Real.sqrt (g z) := by
  let z := B.dualPreimage hPos g
  let w := (Real.sqrt (g z))⁻¹ • z
  have hz_nonneg : 0 ≤ g z := le_of_lt hz
  have hsqrt_pos : 0 < Real.sqrt (g z) := Real.sqrt_pos.2 hz
  have hsqrt_sq : Real.sqrt (g z) * Real.sqrt (g z) = g z := by
    nlinarith [Real.sq_sqrt hz_nonneg]
  have hgw : g w = Real.sqrt (g z) := by
    -- Evaluate `g` on the normalized witness and cancel one factor of `√(g z)`.
    calc
      g w = g z / Real.sqrt (g z) := by
        simp [w, z, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      _ = Real.sqrt (g z) := by
        apply (div_eq_iff hsqrt_pos.ne').2
        exact hsqrt_sq.symm
  have hzw : B z w = g w := by
    simpa [z] using (B.dualPreimage_apply hPos g w)
  have hw_self : B w w = 1 := by
    -- Rewrite the self-pairing through `g w`, then cancel the normalizing factor.
    calc
      B w w = B z w / Real.sqrt (g z) := by
        simp [w, z, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      _ = g w / Real.sqrt (g z) := by rw [hzw]
      _ = Real.sqrt (g z) / Real.sqrt (g z) := by
        rw [hgw]
      _ = 1 := by
        exact div_self hsqrt_pos.ne'
  have hw_norm : B.primalSeminorm hPos w ≤ 1 := by
    -- The normalized witness has primal norm exactly `1`.
    rw [B.primalSeminorm_apply, hw_self]
    norm_num
  exact ⟨hw_norm, hgw⟩

/-- Under symmetry and positive-definiteness, the finite-dimensional `B`-dual norm agrees with the
textbook formula `g ↦ ⟪g, B⁻¹ g⟫^(1/2)`, written through the canonical bridge
`B.dualPreimage hPos g`. -/
theorem dualNorm_apply [FiniteDimensional ℝ E] (B : LinearMap.BilinForm ℝ E) (hSymm : B.IsSymm)
    (hPos : B.toQuadraticMap.PosDef) (g : Dual ℝ E) :
    ‖g‖*[B | hPos] = Real.sqrt (g (B.dualPreimage hPos g)) := by
  let S : Set ℝ := (fun x : E ↦ g x) '' {x | ‖x‖[B | hPos] ≤ 1}
  let z := B.dualPreimage hPos g
  have hz_nonneg : 0 ≤ g z := by
    -- The extremal scalar is nonnegative because it equals the positive quadratic self-pairing.
    rw [dualPreimage_self_pairing]
    exact hPos.nonneg z
  have hS_nonempty : S.Nonempty := by
    -- The primal unit ball contains `0`, so the support image is nonempty.
    refine ⟨0, ⟨0, by simpa [B.primalSeminorm_apply], by simp⟩⟩
  have hS_bdd : BddAbove S := by
    -- The Cauchy-Schwarz estimate bounds every support value by the candidate extremal scalar.
    refine ⟨Real.sqrt (g z), ?_⟩
    rintro y ⟨x, hx, rfl⟩
    simpa [z] using
      dual_eval_le_sqrt_dualPreimage_self_of_primalSeminorm_le_one B hSymm hPos g hx
  rw [dualNorm_eq_sSup_primalUnitBall]
  change sSup S = Real.sqrt (g z)
  refine le_antisymm ?_ ?_
  · -- The support value cannot exceed the Cauchy-Schwarz bound on the unit ball.
    refine csSup_le hS_nonempty ?_
    rintro y ⟨x, hx, rfl⟩
    simpa [z] using
      dual_eval_le_sqrt_dualPreimage_self_of_primalSeminorm_le_one B hSymm hPos g hx
  · by_cases hz : g z = 0
    · -- If the candidate extremal scalar vanishes, `0` in the image forces the supremum to be `0`.
      have hzero_mem : (0 : ℝ) ∈ S := by
        refine ⟨0, ?_, by simp⟩
        simpa [B.primalSeminorm_apply]
      have hsup_nonneg : 0 ≤ sSup S := le_csSup hS_bdd hzero_mem
      simpa [hz] using hsup_nonneg
    · have hz_ne : 0 ≠ g z := by
        simpa [eq_comm] using hz
      have hz_pos : 0 < g z := lt_of_le_of_ne hz_nonneg hz_ne
      let w := (Real.sqrt (g z))⁻¹ • z
      have hw : B.primalSeminorm hPos w ≤ 1 ∧ g w = Real.sqrt (g z) := by
        simpa [z, w] using normalized_dualPreimage_attains_support B hPos g hz_pos
      have hw_mem : g w ∈ S := ⟨w, hw.1, rfl⟩
      -- Insert the normalized witness into the support image to realize the upper bound.
      have hwsup : g w ≤ sSup S := le_csSup hS_bdd hw_mem
      simpa [hw.2] using hwsup

end

end LinearMap.BilinForm
