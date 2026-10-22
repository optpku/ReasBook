/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_5_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_3_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_3_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped BInducedNorm CubicNewtonStepNotation Gradient

universe u

/-- Helper for Lemma 4.3.3: for real continuous linear functionals, the support function of the
ambient closed unit ball equals the operator norm. -/
private theorem ContinuousLinearMap.sSup_unitClosedBall_eq_norm_real
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : F →L[ℝ] ℝ) :
    sSup (g '' Metric.closedBall (0 : F) 1) = ‖g‖ := by
  let S : Set ℝ := g '' Metric.closedBall (0 : F) 1
  let T : Set ℝ := (fun x : F ↦ |g x|) '' Metric.closedBall (0 : F) 1
  have hS_nonempty : S.Nonempty := ⟨0, ⟨0, by simp, by simp⟩⟩
  have hS_bound : ∀ y ∈ S, y ≤ ‖g‖ := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx_norm : ‖x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hgx : |g x| ≤ ‖g‖ * ‖x‖ := by
      simpa [Real.norm_eq_abs] using g.le_opNorm x
    -- Bound each evaluation on the closed unit ball by the operator norm.
    calc
      g x ≤ |g x| := le_abs_self _
      _ ≤ ‖g‖ * ‖x‖ := hgx
      _ ≤ ‖g‖ * 1 := mul_le_mul_of_nonneg_left hx_norm (norm_nonneg _)
      _ = ‖g‖ := by ring
  have hS_bdd : BddAbove S := ⟨‖g‖, hS_bound⟩
  have hT_nonempty : T.Nonempty := ⟨0, ⟨0, by simp, by simp⟩⟩
  have hT_subset : T ⊆ S := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    by_cases hgx : 0 ≤ g x
    · exact ⟨x, hx, by simp [abs_of_nonneg hgx]⟩
    · refine ⟨-x, by simpa [Metric.mem_closedBall, dist_eq_norm] using hx, ?_⟩
      simp [abs_of_neg (lt_of_not_ge hgx)]
  have hsSup_T_le : sSup T ≤ sSup S := by
    refine csSup_le hT_nonempty ?_
    intro y hy
    exact le_csSup hS_bdd (hT_subset hy)
  have hT_eq : sSup T = ‖g‖ := by
    simpa [T, Real.norm_eq_abs] using ContinuousLinearMap.sSup_unitClosedBall_eq_norm g
  have hsSup_S_le : sSup S ≤ ‖g‖ := csSup_le hS_nonempty hS_bound
  have hnorm_le : ‖g‖ ≤ sSup S := by
    rw [← hT_eq]
    exact hsSup_T_le
  -- The absolute-value support formula and symmetry of the ball recover the usual support value.
  exact le_antisymm hsSup_S_le hnorm_le

/-- Helper for Lemma 4.3.3: on the intrinsic carrier `PrimalSpace B`, the generic operator norm
on the continuous dual agrees with the chapter's `B`-dual norm. -/
lemma LinearMap.BilinForm.strongDualNorm_eq_bDualNormOnPrimalSpace
    {F : Type u} [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (B : BilinForm ℝ F) [Fact B.toQuadraticMap.PosDef]
    (g : PrimalSpace B →L[ℝ] ℝ) :
    ‖g‖ = ‖g‖[B,*] := by
  have hball :
      {x : PrimalSpace B | B.primalSeminorm Fact.out x ≤ 1} =
        Metric.closedBall (0 : PrimalSpace B) 1 := by
    ext x
    constructor
    · intro hx
      -- On `PrimalSpace B`, the ambient closed unit ball is cut out by the same norm inequality.
      change B.primalSeminorm Fact.out x ≤ 1 at hx
      have hx' : ‖x‖ ≤ 1 := by
        change B.primalSeminorm Fact.out x ≤ 1
        exact hx
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx'
    · intro hx
      -- Route correction: rewrite the closed-ball condition to an ambient norm inequality first.
      have hx' : ‖x‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx
      change B.primalSeminorm Fact.out x ≤ 1 at hx'
      change B.primalSeminorm Fact.out x ≤ 1
      exact hx'
  -- Rewrite the source dual norm onto the ambient closed unit ball and use the real support
  -- formula for continuous linear functionals.
  rw [LinearMap.BilinForm.dualNorm_eq_sSup_primalUnitBall_strongDual]
  rw [hball]
  symm
  exact ContinuousLinearMap.sSup_unitClosedBall_eq_norm_real g

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Lemma 4.3.3 lies in the bilinear-form-induced cubic-Newton / Hessian-Lipschitz remainder
domain.

Sampled owner-style declarations:
* `HasLipschitzContinuousHessian` in `Definition_4_3_5`, written on theorem surfaces as
  `f ∈ C22[Mf]` on `PrimalSpace B`;
* `HasLipschitzContinuousHessian.gradient_deviation_le` in `Chap01/Lemma_1_5_11`, read on the
  intrinsic carrier `PrimalSpace B`;
* `CubicNewtonStep` in `Definition_4_3_6`, the source-facing owner of the chosen cubic Newton map;
* `CubicNewtonStep.firstOrderOptimalityCondition` in `Definition_4_3_6`, the owner-level
  first-order optimality theorem for the chosen cubic Newton point.

Best owner abstraction:
* source-facing: the cubic Newton step `step : CubicNewtonStep B f M`;
* core/canonical: the owners `((f : PrimalSpace B → ℝ) ∈ C22[Mf])` and
  `CubicNewtonStep B f M`;
* bridge/view: the gradient remainder estimate along `step x - x` and the scalar optimality
  identity obtained from the minimizing property of `step`.

Primitive data:
* the bilinear form `B`;
* the positive-definite quadratic data of `B`;
* the canonical Hessian-Lipschitz owner instance on `PrimalSpace B`;
* the chosen cubic Newton step `step`.

Derived API:
* the owner gradient Taylor remainder bound `HasLipschitzContinuousHessian.gradient_deviation_le`
  between arbitrary points `x` and `y`;
* the scalar pairing of the owner-level first-order optimality condition with the displacement
  `step x - x`;
* the lower bounds of Lemma 4.3.3 built from those owner theorems.

The previous file stored the remainder estimate and scalar optimality relation as separate local
`Prop` wrappers, and then specialized the remainder theorem directly to `y = step x`. Those were
not new mathematical owners; they were derived API that should sit on the existing owners
`HasLipschitzContinuousHessian` and `CubicNewtonStep`. This refinement deletes the duplicate
wrapper layer and uses the Chapter 1 remainder theorem together with the owner-level first-order
optimality theorem on `CubicNewtonStep` directly.
-/

section

variable {B : BilinForm ℝ E} {Mf : NNReal} {f : PrimalSpace B → ℝ}
variable [Fact B.toQuadraticMap.PosDef]

attribute [local instance]
  LinearMap.BilinForm.instNormedAddCommGroupPrimalSpaceOfFactPosDefRealToQuadraticMap
attribute [local instance] LinearMap.BilinForm.instNormedSpaceRealPrimalSpace

/-- Helper for Lemma 4.3.3: this local alias fixes the `C22` owner surface to the chapter's
`B`-induced normed structure on `PrimalSpace B`, so later helper statements do not drift onto the
inherited Hilbert-space spelling. -/
private abbrev primalSpaceMemC22
    (Mf : NNReal) (f : PrimalSpace B → ℝ) : Prop :=
  f ∈ C22[Mf]

omit [FiniteDimensional ℝ E] in
/-- Helper for Lemma 4.3.3: the symmetric associated bilinear form carries the same positive
quadratic data as `B`, so the Chapter 4.3 geometry can be transferred to the symmetric surface
used by Proposition 4.3.3. -/
lemma associated_posDef :
    (B.toQuadraticMap.associated).toQuadraticMap.PosDef := by
  -- The associated form has the same diagonal quadratic form, so positivity is unchanged.
  rw [QuadraticMap.posDef_iff_nonneg]
  let hPos : B.toQuadraticMap.PosDef := Fact.out
  refine ⟨?_, ?_⟩
  · intro z
    rw [show (B.toQuadraticMap.associated).toQuadraticMap z = B.toQuadraticMap z by
      simpa using QuadraticMap.associated_eq_self_apply ℝ B.toQuadraticMap z]
    exact hPos.nonneg z
  · intro z hz
    apply hPos.anisotropic z
    rw [← show (B.toQuadraticMap.associated).toQuadraticMap z = B.toQuadraticMap z by
      simpa using QuadraticMap.associated_eq_self_apply ℝ B.toQuadraticMap z]
    exact hz

/-- Helper for Lemma 4.3.3: typeclass search can use the positive-definite quadratic data of the
associated symmetric form. -/
instance associatedPosDefFact : Fact (B.toQuadraticMap.associated).toQuadraticMap.PosDef :=
  ⟨associated_posDef⟩

/-- Helper for Lemma 4.3.3: the associated symmetric form induces the same primal norm as `B`
because both forms have the same quadratic map on diagonal values. -/
lemma associated_primal_norm_eq
    {F : Type u} [AddCommGroup F] [Module ℝ F]
    (B : BilinForm ℝ F) [Fact B.toQuadraticMap.PosDef]
    [Fact (B.toQuadraticMap.associated).toQuadraticMap.PosDef] (z : F) :
    ‖z‖[B.toQuadraticMap.associated] = ‖z‖[B] := by
  -- Rewrite both norms by their diagonal formulas and use `associated_eq_self_apply`.
  rw [LinearMap.BilinForm.primalSeminorm_apply, LinearMap.BilinForm.primalSeminorm_apply]
  simpa using
    congrArg Real.sqrt (QuadraticMap.associated_eq_self_apply ℝ B.toQuadraticMap z)

/-- Helper for Lemma 4.3.3: the dual support function is unchanged after replacing `B` by its
associated symmetric form because the primal unit ball is unchanged. -/
lemma associated_dual_norm_eq
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (B : BilinForm ℝ F) [Fact B.toQuadraticMap.PosDef]
    [Fact (B.toQuadraticMap.associated).toQuadraticMap.PosDef] (g : F →L[ℝ] ℝ) :
    ‖g‖[B.toQuadraticMap.associated,*] = ‖g‖[B,*] := by
  -- Rewrite both dual norms onto the same support-function set cut out by the primal unit ball.
  rw [LinearMap.BilinForm.dualNorm_eq_sSup_primalUnitBall_strongDual,
    LinearMap.BilinForm.dualNorm_eq_sSup_primalUnitBall_strongDual]
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzA : ‖z‖[B.toQuadraticMap.associated] ≤ 1 := by
      simpa using hz
    have hzB : ‖z‖[B] ≤ 1 := by
      rwa [associated_primal_norm_eq B z] at hzA
    exact ⟨z, by
      simpa using hzB, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    have hzB : ‖z‖[B] ≤ 1 := by
      simpa using hz
    have hzA : ‖z‖[B.toQuadraticMap.associated] ≤ 1 := by
      rwa [associated_primal_norm_eq B z]
    exact ⟨z, by
      simpa using hzA, rfl⟩

/-- Helper for Lemma 4.3.3: the cubic Newton model is unchanged after passing to the associated
form because the cubic penalty depends only on the induced norm. -/
lemma cubicNewtonModel_associated_eq
    {M : ℝ} (x T : E) :
    cubicNewtonModel B.toQuadraticMap.associated f M x T =
      cubicNewtonModel B f M x T := by
  -- Route correction: keep the source cubic model intact and only rewrite the norm surface.
  rw [cubicNewtonModel_apply, cubicNewtonModel_apply,
    associated_primal_norm_eq B (T - x)]

/-- Helper for Lemma 4.3.3: the original cubic Newton minimizer is still a minimizer for the
associated symmetric model because the two models agree pointwise. -/
lemma associated_cubicNewtonStep_isMinOn
    {M : ℝ} (step : CubicNewtonStep B f M) (x : E) :
    IsMinOn (cubicNewtonModel B.toQuadraticMap.associated f M x) Set.univ (step x) := by
  -- Transfer the minimizing property pointwise across the identical cubic model.
  intro y hy
  simpa [cubicNewtonModel_associated_eq x] using
    step.isMinOn_apply x hy

/-- Helper for Lemma 4.3.3: the given cubic Newton map can be viewed on the associated symmetric
surface without changing its values. -/
abbrev associated_cubicNewtonStep
    {M : ℝ} (step : CubicNewtonStep B f M) :
    CubicNewtonStep B.toQuadraticMap.associated f M :=
  { toFun := step
    isMinOn := associated_cubicNewtonStep_isMinOn step }

/-- Helper for Lemma 4.3.3: in finite dimension, the bilinear-form covector `A d` is used as a
continuous linear functional through the canonical linear-to-continuous bridge. -/
abbrev bilinCovector
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (A : BilinForm ℝ F) (d : F) : F →L[ℝ] ℝ :=
  ((LinearMap.toContinuousLinearMap : (F →ₗ[ℝ] ℝ) ≃ₗ[ℝ] F →L[ℝ] ℝ) (A d))

/-- Helper for Lemma 4.3.3: adding the bilinear-form covector `a • A d` shifts the canonical
dual preimage by the corresponding primal vector `a • d`. -/
lemma dualPreimage_add_bilin_smul
    {A : BilinForm ℝ E} [Fact A.toQuadraticMap.PosDef]
    (g : E →L[ℝ] ℝ) (d : E) (a : ℝ) :
    A.dualPreimage Fact.out (g.toLinearMap + a • A d) =
      A.dualPreimage Fact.out g.toLinearMap + a • d := by
  -- Evaluate both candidate preimages against `A` and use injectivity of the `A.toDual` bridge.
  let hnd : A.Nondegenerate := A.nondegenerate_of_posDef Fact.out
  apply (A.toDual hnd).injective
  ext u
  simp [LinearMap.BilinForm.dualPreimage, LinearMap.BilinForm.toDual_def, map_add, map_smul]

/-- Helper for Lemma 4.3.3: for a symmetric positive-definite form, the square of the dual norm
of a covector is the self-pairing of its canonical dual preimage. -/
lemma dualNorm_sq_eq_self_pairing
    {A : BilinForm ℝ E} [Fact A.toQuadraticMap.PosDef]
    (hSymm : A.IsSymm) (g : E →L[ℝ] ℝ) :
    ‖g‖[A,*] ^ (2 : ℕ) = g (A.dualPreimage Fact.out g.toLinearMap) := by
  -- Rewrite the dual norm by the `A.dualPreimage` formula and square the resulting square root.
  let hPos : A.toQuadraticMap.PosDef := Fact.out
  have hz_nonneg : 0 ≤ g (A.dualPreimage Fact.out g.toLinearMap) := by
    simpa using hPos.nonneg (A.dualPreimage Fact.out g.toLinearMap)
  calc
    ‖g‖[A,*] ^ (2 : ℕ) =
        (Real.sqrt (g (A.dualPreimage Fact.out g.toLinearMap))) ^ (2 : ℕ) := by
          rw [LinearMap.BilinForm.dualNorm_apply_strongDual A hSymm Fact.out g]
    _ = g (A.dualPreimage Fact.out g.toLinearMap) := by
          simp [hz_nonneg]

/-- Helper for Lemma 4.3.3: on a symmetric positive-definite surface, the square of the shifted
dual norm expands quadratically in the shift coefficient. -/
lemma shiftedDualNormSq_eq
    {A : BilinForm ℝ E} [Fact A.toQuadraticMap.PosDef]
    (hSymm : A.IsSymm) (g : E →L[ℝ] ℝ) (d : E) (a : ℝ) :
    ‖g + a • bilinCovector A d‖[A,*] ^ (2 : ℕ) =
      ‖g‖[A,*] ^ (2 : ℕ) + 2 * a * g d + a ^ (2 : ℕ) * ‖d‖[A] ^ (2 : ℕ) := by
  let r : ℝ := ‖d‖[A]
  let u : E := A.dualPreimage Fact.out g.toLinearMap
  let shift : E →L[ℝ] ℝ := g + a • bilinCovector A d
  have hnorm_sq : r ^ (2 : ℕ) = A d d := by
    dsimp [r]
    rw [LinearMap.BilinForm.primalSeminorm_apply]
    have hA_nonneg : 0 ≤ (A d) d := by
      change 0 ≤ A.toQuadraticMap d
      exact QuadraticMap.PosDef.nonneg Fact.out d
    simpa [pow_two] using (Real.sq_sqrt hA_nonneg)
  have hpair_g :
      ‖g‖[A,*] ^ (2 : ℕ) = A u u := by
    simpa [u] using dualNorm_sq_eq_self_pairing hSymm g
  have hpair_shift :
      ‖shift‖[A,*] ^ (2 : ℕ) = shift (A.dualPreimage Fact.out shift.toLinearMap) := by
    exact dualNorm_sq_eq_self_pairing hSymm shift
  have hpreimage :
      A.dualPreimage Fact.out shift.toLinearMap = u + a • d := by
    simpa [u, shift] using dualPreimage_add_bilin_smul g d a
  have hud : A u d = g d := by
    simpa only [u] using A.dualPreimage_apply Fact.out g.toLinearMap d
  have hdu : A d u = g d := by
    rw [hSymm.eq d u, hud]
  have hdd : A d d = ‖d‖[A] ^ (2 : ℕ) := by
    exact hnorm_sq.symm
  have hgu :
      g (u + a • d) = A u (u + a • d) := by
    simpa only [u] using (A.dualPreimage_apply Fact.out g.toLinearMap (u + a • d)).symm
  calc
    ‖g + a • bilinCovector A d‖[A,*] ^ (2 : ℕ) = ‖shift‖[A,*] ^ (2 : ℕ) := by
      rfl
    _ = shift (A.dualPreimage Fact.out shift.toLinearMap) := hpair_shift
    _ = shift (u + a • d) := by
          rw [hpreimage]
    _ = g (u + a • d) + a * (bilinCovector A d) (u + a • d) := by
          simp [shift]
    _ = A u (u + a • d) + a * A d (u + a • d) := by
      rw [hgu]
      simp [bilinCovector]
    _ = A u u + a * A u d + (a * A d u + a ^ (2 : ℕ) * A d d) := by
          rw [(A u).map_add, (A d).map_add, (A u).map_smul, (A d).map_smul]
          ring
    _ = A u u + 2 * a * g d + a ^ (2 : ℕ) * ‖d‖[A] ^ (2 : ℕ) := by
          rw [hud, hdu, hdd]
          ring
    _ = ‖g‖[A,*] ^ (2 : ℕ) + 2 * a * g d + a ^ (2 : ℕ) * ‖d‖[A] ^ (2 : ℕ) := by
          rw [hpair_g]

/-- Helper for Lemma 4.3.3: the associated symmetric form measures the step displacement by the
same radius `r_M(x)` as the original form `B`. -/
lemma associated_stepDisplacement_norm_eq_residual
    {M : ℝ} (step : CubicNewtonStep B f M) (x : E) :
    ‖step x - x‖[B.toQuadraticMap.associated] = r[step](x) := by
  -- This is the stable norm-transport identity needed when the proof moves to the associated form.
  rw [associated_primal_norm_eq B (step x - x), CubicNewtonStep.residual_apply]

/-- Helper for Lemma 4.3.3: on `PrimalSpace B`, the associated-form residual rewrite stays in the
single intrinsic spelling needed by the final lower-bound proof. -/
private lemma associatedStepResidualNormEq
    {M : ℝ} (step : CubicNewtonStep B f M) (x : PrimalSpace B) :
    ‖step x - x‖[B.toQuadraticMap.associated] = r[step](x) := by
  -- Reuse the ambient residual rewrite on the intrinsic carrier without changing spelling worlds.
  simpa using associated_stepDisplacement_norm_eq_residual step x

/-- Helper for Lemma 4.3.3: finite dimensionality on `E` transfers to the intrinsic carrier
`PrimalSpace B`, so the later norm bridges do not need repeated local instance setup. -/
private instance primalSpaceFiniteDimensional :
    FiniteDimensional ℝ (PrimalSpace B) := by
  change FiniteDimensional ℝ E
  infer_instance

/-- Helper for Lemma 4.3.3: finite dimensionality makes the `B`-induced primal space complete,
so the Banach-valued fundamental theorem of calculus applies on the intrinsic carrier. -/
private instance primalSpaceCompleteSpace :
    CompleteSpace (PrimalSpace B) := by
  infer_instance

/-- Helper for Lemma 4.3.3: on `PrimalSpace B`, replacing `B` by its associated symmetric form
does not change the chapter dual norm. -/
private lemma associatedDualNormEqOnPrimalSpace
    (g : PrimalSpace B →L[ℝ] ℝ) :
    ‖g‖[B.toQuadraticMap.associated,*] = ‖g‖[B,*] := by
  -- Route correction: keep the dual-norm rewrite localized to `PrimalSpace B`.
  simpa using associated_dual_norm_eq B g

/-- Helper for Lemma 4.3.3: if the `A`-radius of the displacement vanishes, positive
definiteness forces `d = 0`, so the lower bound degenerates to the trivial identity `0 ≥ 0`. -/
lemma dualPairingLowerBoundOfDualShiftBoundZero
    {A : BilinForm ℝ E} [Fact A.toQuadraticMap.PosDef]
    {M Mf : ℝ}
    (d : E) (g : E →L[ℝ] ℝ)
    (hd0 : ‖d‖[A] = 0) :
    g (-d) ≥
      (1 / (M * ‖d‖[A])) * ‖g‖[A,*] ^ (2 : ℕ) +
        ((M ^ (2 : ℕ) - Mf ^ (2 : ℕ)) / (4 * M)) * ‖d‖[A] ^ (3 : ℕ) := by
  -- Vanishing `A`-radius forces `d = 0`, so every term in the target inequality collapses.
  have hd : d = 0 := by
    rw [LinearMap.BilinForm.primalSeminorm_apply] at hd0
    have hA_nonneg : 0 ≤ (A d) d := by
      change 0 ≤ A.toQuadraticMap d
      exact QuadraticMap.PosDef.nonneg Fact.out d
    have hsq0 : (Real.sqrt ((A d) d)) ^ (2 : ℕ) = 0 := by
      rw [hd0]
      norm_num
    have hdd_zero : (A d) d = 0 := by
      calc
        (A d) d = (Real.sqrt ((A d) d)) ^ (2 : ℕ) := by
          symm
          simpa [pow_two] using (Real.sq_sqrt hA_nonneg)
        _ = 0 := hsq0
    exact (QuadraticMap.PosDef.anisotropic Fact.out d) <| by
      change A.toQuadraticMap d = 0
      simpa using hdd_zero
  simp [hd]

/-- Helper for Lemma 4.3.3: in the positive-radius branch, squaring the shifted dual estimate and
expanding the `A.dualPreimage` expression yields the full algebraic lower bound. -/
lemma dualPairingLowerBoundOfDualShiftBoundPos
    {A : BilinForm ℝ E} [Fact A.toQuadraticMap.PosDef]
    (hSymm : A.IsSymm) {M Mf : ℝ} (hM : 0 < M)
    (d : E) (g : E →L[ℝ] ℝ)
    (hd_pos : 0 < ‖d‖[A])
    (hshift :
      ‖g + (((M / 2 : ℝ) * ‖d‖[A]) • bilinCovector A d)‖[A,*] ≤
        ((Mf : ℝ) / 2) * ‖d‖[A] ^ (2 : ℕ)) :
    g (-d) ≥
      (1 / (M * ‖d‖[A])) * ‖g‖[A,*] ^ (2 : ℕ) +
        ((M ^ (2 : ℕ) - Mf ^ (2 : ℕ)) / (4 * M)) * ‖d‖[A] ^ (3 : ℕ) := by
  let r : ℝ := ‖d‖[A]
  let a : ℝ := ((M / 2 : ℝ) * r)
  let shift : E →L[ℝ] ℝ := g + (a • bilinCovector A d)
  have hshift_nonneg : 0 ≤ ‖shift‖[A,*] := by
    rw [LinearMap.BilinForm.dualNorm_apply_strongDual A hSymm Fact.out shift]
    exact Real.sqrt_nonneg _
  have hshift_rhs_nonneg : 0 ≤ ((Mf : ℝ) / 2) * r ^ (2 : ℕ) := by
    exact le_trans hshift_nonneg <| by
      simpa [r, a, shift] using hshift
  have hsq :
      ‖shift‖[A,*] ^ (2 : ℕ) ≤
        (((Mf : ℝ) / 2) * r ^ (2 : ℕ)) ^ (2 : ℕ) := by
    exact (sq_le_sq₀ hshift_nonneg hshift_rhs_nonneg).2 <| by
      simpa [r, a, shift] using hshift
  have hleft_expand :
      ‖shift‖[A,*] ^ (2 : ℕ) =
        ‖g‖[A,*] ^ (2 : ℕ) + M * r * g d +
          (M ^ (2 : ℕ) / 4) * r ^ (4 : ℕ) := by
    -- Reuse the standalone quadratic expansion for the shifted dual norm.
    calc
      ‖shift‖[A,*] ^ (2 : ℕ) = ‖g + a • bilinCovector A d‖[A,*] ^ (2 : ℕ) := by
            rfl
      _ = ‖g‖[A,*] ^ (2 : ℕ) + 2 * a * g d + a ^ (2 : ℕ) * ‖d‖[A] ^ (2 : ℕ) := by
            exact shiftedDualNormSq_eq hSymm g d a
      _ = ‖g‖[A,*] ^ (2 : ℕ) + M * r * g d +
            (M ^ (2 : ℕ) / 4) * r ^ (4 : ℕ) := by
            dsimp [a, r]
            ring
  have hrhs_sq :
      (((Mf : ℝ) / 2) * r ^ (2 : ℕ)) ^ (2 : ℕ) =
        ((Mf ^ (2 : ℕ)) / 4) * r ^ (4 : ℕ) := by
    ring_nf
  have hbound :
      ‖g‖[A,*] ^ (2 : ℕ) + M * r * g d +
          (M ^ (2 : ℕ) / 4) * r ^ (4 : ℕ) ≤
        ((Mf ^ (2 : ℕ)) / 4) * r ^ (4 : ℕ) := by
    rw [hleft_expand, hrhs_sq] at hsq
    exact hsq
  have hbound' :
      ‖g‖[A,*] ^ (2 : ℕ) + M * r * g d ≤
        ((Mf ^ (2 : ℕ) - M ^ (2 : ℕ)) / 4) * r ^ (4 : ℕ) := by
    nlinarith [hbound]
  have hnum :
      M * r * g (-d) ≥
        ‖g‖[A,*] ^ (2 : ℕ) +
          ((M ^ (2 : ℕ) - Mf ^ (2 : ℕ)) / 4) * r ^ (4 : ℕ) := by
    -- Move the cross term to the target side and rewrite it through `g (-d) = -g d`.
    have hneg : g (-d) = -g d := by
      simp
    rw [hneg]
    nlinarith [hbound']
  -- Divide the numerator inequality by the positive factor `M * r`.
  have hMr_pos : 0 < M * r := by
    dsimp [r]
    exact mul_pos hM hd_pos
  have hquot :
      (‖g‖[A,*] ^ (2 : ℕ) +
          ((M ^ (2 : ℕ) - Mf ^ (2 : ℕ)) / 4) * r ^ (4 : ℕ)) / (M * r) ≤
        g (-d) := by
    apply (div_le_iff₀ hMr_pos).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hnum
  have hrepr :
      (‖g‖[A,*] ^ (2 : ℕ) +
          ((M ^ (2 : ℕ) - Mf ^ (2 : ℕ)) / 4) * r ^ (4 : ℕ)) / (M * r) =
        (1 / (M * r)) * ‖g‖[A,*] ^ (2 : ℕ) +
          ((M ^ (2 : ℕ) - Mf ^ (2 : ℕ)) / (4 * M)) * r ^ (3 : ℕ) := by
    field_simp [hM.ne', hd_pos.ne']
  rw [← hrepr]
  exact hquot

/-- Helper for Lemma 4.3.3: once the shifted covector is controlled in the associated dual norm,
expanding the `A.dualPreimage` square gives the source lower bound on the gradient pairing. -/
lemma dual_pairing_lower_bound_of_dual_shift_bound
    {A : BilinForm ℝ E} [Fact A.toQuadraticMap.PosDef]
    (hSymm : A.IsSymm) {M Mf : ℝ} (hM : 0 < M)
    (d : E) (g : E →L[ℝ] ℝ)
    (hshift :
      ‖g + (((M / 2 : ℝ) * ‖d‖[A]) • bilinCovector A d)‖[A,*] ≤
        ((Mf : ℝ) / 2) * ‖d‖[A] ^ (2 : ℕ)) :
    g (-d) ≥
      (1 / (M * ‖d‖[A])) * ‖g‖[A,*] ^ (2 : ℕ) +
        ((M ^ (2 : ℕ) - Mf ^ (2 : ℕ)) / (4 * M)) * ‖d‖[A] ^ (3 : ℕ) := by
  by_cases hd0 : ‖d‖[A] = 0
  · -- The zero-radius branch collapses to the trivial identity after positivity forces `d = 0`.
    exact dualPairingLowerBoundOfDualShiftBoundZero d g hd0
  · have hd_nonneg : 0 ≤ ‖d‖[A] := by
      rw [LinearMap.BilinForm.primalSeminorm_apply]
      exact Real.sqrt_nonneg _
    have hd_pos : 0 < ‖d‖[A] := lt_of_le_of_ne hd_nonneg (Ne.symm hd0)
    -- In the positive-radius branch, reuse the already-expanded algebraic estimate verbatim.
    exact dualPairingLowerBoundOfDualShiftBoundPos hSymm hM d g hd_pos hshift

/-- Helper for Lemma 4.3.3: the coefficient from `(4.3.13)` dominates the sigma-dependent
coefficient from `(4.3.14)` once `M ≥ M_f / σ` with `σ ∈ (0, 1]`. -/
lemma sigma_cubic_coefficient_lower_bound
    {M σ : ℝ}
    (hσ : σ ∈ Set.Ioc (0 : ℝ) 1)
    (hMσ : M ≥ (1 / σ) * (Mf : ℝ))
    (hM : 0 < M) :
    ((1 - σ ^ (2 : ℕ)) / 4 : ℝ) * M ≤
      (M ^ (2 : ℕ) - (Mf : ℝ) ^ (2 : ℕ)) / (4 * M) := by
  have hσ_pos : 0 < σ := hσ.1
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ_pos
  have hMf_le : (Mf : ℝ) ≤ σ * M := by
    have hσ_mul :=
      mul_le_mul_of_nonneg_left hMσ hσ_pos.le
    calc
      (Mf : ℝ) = σ * ((1 / σ) * (Mf : ℝ)) := by
        field_simp [hσ_ne]
      _ ≤ σ * M := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hσ_mul
  have hsq : (Mf : ℝ) ^ (2 : ℕ) ≤ σ ^ (2 : ℕ) * M ^ (2 : ℕ) := by
    nlinarith
  field_simp [hM.ne']
  nlinarith

omit [Fact B.toQuadraticMap.PosDef] in
/-- Helper for Lemma 4.3.3: a local `C²` hypothesis identifies the gradient covector with the
Fréchet derivative on `PrimalSpace B`. -/
private lemma gradientCovector_eq_fderivAt
    {z : PrimalSpace B} (hcont : ContDiffAt ℝ 2 f z) :
    (InnerProductSpace.toDual ℝ (PrimalSpace B)) (∇ f z) =
      fderiv ℝ f z := by
  -- Keep the gradient bridge on the inherited Hilbert surface, with the `C²` hypothesis made
  -- explicit so no owner-level transport theorem is needed.
  simpa using
    (((hcont.differentiableAt (by norm_num)).hasGradientAt.hasFDerivAt.fderiv).symm)

omit [FiniteDimensional ℝ E] [Fact B.toQuadraticMap.PosDef] in
/-- Helper for Lemma 4.3.3: the affine segment `s ↦ x + s • d` on `PrimalSpace B` has derivative
`d`. -/
private lemma primalLine_hasDerivAt
    (x d : PrimalSpace B) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

section GenericFderivRemainder

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {L3 : NNReal} {g : X → ℝ}

omit [CompleteSpace X] in
/-- Helper for Lemma 4.3.3: on any real normed space, the affine segment `s ↦ x + s • d` has
derivative `d`. -/
private lemma genericLine_hasDerivAt
    (x d : X) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate the scalar multiple and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

omit [CompleteSpace X] in
/-- Helper for Lemma 4.3.3: the affine segment of the Fréchet derivative integrates to the exact
first-order increment of `fderiv ℝ g`. -/
private lemma segment_fderiv_integral_eq_generic
    (hg : g ∈ C22[L3])
    (x d : X) :
    fderiv ℝ g (x + d) - fderiv ℝ g x =
      ∫ t in 0..1, fderiv ℝ (fderiv ℝ g) (x + t • d) d := by
  have hderiv :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ ↦ fderiv ℝ g (x + s • d))
          (fderiv ℝ (fderiv ℝ g) (x + t • d) d) t := by
    intro t ht
    have hcontAt : ContDiffAt ℝ 1 (fderiv ℝ g) (x + t • d) :=
      (hg.contDiff.contDiffAt (x := x + t • d)).fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    -- Differentiate the derivative field after restricting it to the affine segment.
    simpa [Function.comp] using
      hcontAt.differentiableAt one_ne_zero |>.hasFDerivAt.comp_hasDerivAt t
        (genericLine_hasDerivAt x d t)
  have hcont :
      Continuous (fun t : ℝ ↦ fderiv ℝ (fderiv ℝ g) (x + t • d) d) := by
    have hcontFDeriv :
        Continuous (fun t : ℝ ↦ fderiv ℝ (fderiv ℝ g) (x + t • d)) :=
      hg.sndFDeriv_lipschitz.continuous.comp
        (continuous_const.add (continuous_id.smul continuous_const))
    exact hcontFDeriv.clm_apply continuous_const
  have hint :
      IntervalIntegrable (fun t : ℝ ↦ fderiv ℝ (fderiv ℝ g) (x + t • d) d)
        MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable 0 1
  -- Apply Banach-valued FTC to the derivative field on the segment.
  symm
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

omit [CompleteSpace X] in
/-- Helper for Lemma 4.3.3: the Hessian-Lipschitz owner estimate controls the action of the
second Fréchet derivative increment along a segment direction. -/
private lemma segment_sndFDeriv_action_bound_generic
    (hg : g ∈ C22[L3])
    (x d : X)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖(fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x) d‖
      ≤ (L3 : ℝ) * t * ‖d‖ ^ (2 : ℕ) := by
  have hnorm :
      ‖fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x‖
        ≤ (L3 : ℝ) * ‖t • d‖ := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      HasLipschitzContinuousHessian.sndFDeriv_norm_sub_le hg (x + t • d) x
  -- Convert the operator-norm bound into an action bound on the displacement vector.
  calc
    ‖(fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x) d‖
      ≤ ‖fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x‖ * ‖d‖ := by
          exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((L3 : ℝ) * ‖t • d‖) * ‖d‖ := by
          gcongr
    _ = ((L3 : ℝ) * (t * ‖d‖)) * ‖d‖ := by
          rw [norm_smul, Real.norm_of_nonneg ht.1]
    _ = (L3 : ℝ) * t * ‖d‖ ^ (2 : ℕ) := by
          ring

namespace HasLipschitzContinuousHessian

omit [CompleteSpace X] in
/-- Helper for Lemma 4.3.3: on a complete real normed space, the first-order Taylor remainder of
`fderiv ℝ g` is controlled by the global Lipschitz constant of `x ↦ D²g(x)`. -/
private lemma fderivRemainderNorm_le
    (hg : g ∈ C22[L3])
    (x y : X) :
    ‖fderiv ℝ g y - fderiv ℝ g x - fderiv ℝ (fderiv ℝ g) x (y - x)‖ ≤
      ((L3 : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  let d : X := y - x
  have hy : x + d = y := by
    simp [d]
  have hcontIntegrand :
      Continuous (fun t : ℝ ↦
        (fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x) d) := by
    have hcontFDeriv :
        Continuous (fun t : ℝ ↦
          fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x) :=
      (hg.sndFDeriv_lipschitz.continuous.comp
        (continuous_const.add (continuous_id.smul continuous_const))).sub continuous_const
    exact hcontFDeriv.clm_apply continuous_const
  have hintIntegrand :
      IntervalIntegrable
        (fun t : ℝ ↦
          (fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x) d)
        MeasureTheory.volume 0 1 :=
    hcontIntegrand.intervalIntegrable 0 1
  have hintBound :
      IntervalIntegrable (fun t : ℝ ↦ (L3 : ℝ) * t * ‖d‖ ^ (2 : ℕ))
        MeasureTheory.volume 0 1 :=
    ((continuous_const.mul continuous_id).mul continuous_const).intervalIntegrable 0 1
  have hmono :
      ∫ t in 0..1,
          ‖(fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x) d‖
        ≤ ∫ t in 0..1, (L3 : ℝ) * t * ‖d‖ ^ (2 : ℕ) := by
    -- Bound the Banach-valued integrand pointwise on the whole segment.
    refine intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
      hintIntegrand.norm hintBound ?_
    intro t ht
    exact segment_sndFDeriv_action_bound_generic (hg := hg) (x := x) (d := d) ht
  have hrewrite :
      fderiv ℝ g y - fderiv ℝ g x - fderiv ℝ (fderiv ℝ g) x d =
        ∫ t in 0..1,
          (fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x) d := by
    -- Rewrite the remainder as an integral of second-derivative differences.
    rw [← hy, segment_fderiv_integral_eq_generic (hg := hg) (x := x) (d := d)]
    have hconst :
        fderiv ℝ (fderiv ℝ g) x d =
          ∫ t in 0..1, fderiv ℝ (fderiv ℝ g) x d := by
      simp
    rw [hconst]
    have hsub0 :
        ∫ t in 0..1, fderiv ℝ (fderiv ℝ g) (x + t • d) d - fderiv ℝ (fderiv ℝ g) x d =
          (∫ t in 0..1, fderiv ℝ (fderiv ℝ g) (x + t • d) d) -
            ∫ t in 0..1, fderiv ℝ (fderiv ℝ g) x d := by
      simpa using
        (intervalIntegral.integral_sub
          (f := fun t : ℝ ↦ fderiv ℝ (fderiv ℝ g) (x + t • d) d)
          (g := fun _ : ℝ ↦ fderiv ℝ (fderiv ℝ g) x d)
          (μ := MeasureTheory.volume)
          (((hg.sndFDeriv_lipschitz.continuous.comp
              (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
                continuous_const).intervalIntegrable 0 1)
          (continuous_const.intervalIntegrable 0 1))
    have hsub :
        (∫ t in 0..1, fderiv ℝ (fderiv ℝ g) (x + t • d) d) -
            ∫ t in 0..1, fderiv ℝ (fderiv ℝ g) x d =
          ∫ t in 0..1, fderiv ℝ (fderiv ℝ g) (x + t • d) d -
            fderiv ℝ (fderiv ℝ g) x d := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub0.symm
    calc
      (∫ t in 0..1, fderiv ℝ (fderiv ℝ g) (x + t • d) d) -
          ∫ t in 0..1, fderiv ℝ (fderiv ℝ g) x d =
        ∫ t in 0..1, fderiv ℝ (fderiv ℝ g) (x + t • d) d -
          fderiv ℝ (fderiv ℝ g) x d := hsub
      _ = ∫ t in 0..1,
            (fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x) d := by
            refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro t ht
            simp
  -- Integrate the pointwise second-derivative bound and compute `∫₀¹ t = 1 / 2`.
  simpa [d] using
    calc
      ‖fderiv ℝ g y - fderiv ℝ g x - fderiv ℝ (fderiv ℝ g) x d‖
        = ‖∫ t in 0..1,
            (fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x) d‖ := by
              rw [hrewrite]
      _ ≤ ∫ t in 0..1,
            ‖(fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x) d‖ := by
              exact intervalIntegral.norm_integral_le_integral_norm
                (f := fun t : ℝ ↦
                  (fderiv ℝ (fderiv ℝ g) (x + t • d) - fderiv ℝ (fderiv ℝ g) x) d)
                (a := (0 : ℝ)) (b := 1) (show (0 : ℝ) ≤ 1 by norm_num)
      _ ≤ ∫ t in 0..1, (L3 : ℝ) * t * ‖d‖ ^ (2 : ℕ) := hmono
      _ = ((L3 : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
            calc
              ∫ t in 0..1, (L3 : ℝ) * t * ‖d‖ ^ (2 : ℕ)
                = ∫ t in 0..1, ((L3 : ℝ) * ‖d‖ ^ (2 : ℕ)) * t := by
                    congr with t
                    ring
              _ = ((L3 : ℝ) * ‖d‖ ^ (2 : ℕ)) * (1 / 2 : ℝ) := by
                    rw [intervalIntegral.integral_const_mul, integral_id]
                    norm_num
              _ = ((L3 : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
                    ring

end HasLipschitzContinuousHessian

end GenericFderivRemainder

omit [Fact B.toQuadraticMap.PosDef] in
/-- Helper for Lemma 4.3.3: the inverse Riesz map identifies a continuous covector on
`PrimalSpace B` with its representing primal vector. -/
private def strongDualToPrimalMap :
    StrongDual ℝ (PrimalSpace B) →L[ℝ] PrimalSpace B :=
  (InnerProductSpace.toDual ℝ (PrimalSpace B)).symm.toContinuousLinearEquiv.toContinuousLinearMap

omit [Fact B.toQuadraticMap.PosDef] in
/-- Helper for Lemma 4.3.3: the Riesz map identifies a primal vector on `PrimalSpace B` with the
corresponding continuous covector. -/
private def primalToStrongDualMap :
    PrimalSpace B →L[ℝ] StrongDual ℝ (PrimalSpace B) :=
  (InnerProductSpace.toDual ℝ (PrimalSpace B)).toContinuousLinearEquiv.toContinuousLinearMap

omit [Fact B.toQuadraticMap.PosDef] in
/-- Helper for Lemma 4.3.3: on `PrimalSpace B`, the second Fréchet derivative is the Hessian
transported through the Riesz map. -/
private lemma sndFDeriv_eq_toDual_comp_hessian_onPrimalSpace
    {x : PrimalSpace B} (hcont : ContDiffAt ℝ 2 f x) :
    fderiv ℝ (fderiv ℝ f) x = primalToStrongDualMap.comp (hessian f x) := by
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    have hfderiv : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
      hcont.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    exact hfderiv.differentiableAt one_ne_zero
  have hhess :
      hessian f x = strongDualToPrimalMap.comp (fderiv ℝ (fderiv ℝ f) x) := by
    -- Route correction: prove the operator-level Riesz identity once, then evaluate it at `d`.
    simpa [gradient, hessian, strongDualToPrimalMap] using
      fderiv_comp x strongDualToPrimalMap.differentiableAt hfdiff
  -- Evaluate the operator identity on arbitrary directions to compare both sides pointwise.
  ext d u
  have happly : hessian f x d = strongDualToPrimalMap (fderiv ℝ (fderiv ℝ f) x d) := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun T => T d) hhess
  have hD :
      strongDualToPrimalMap (fderiv ℝ (fderiv ℝ f) x d) =
        (InnerProductSpace.toDual ℝ (PrimalSpace B)).symm (fderiv ℝ (fderiv ℝ f) x d) := by
    rfl
  calc
    (fderiv ℝ (fderiv ℝ f) x d) u
        = (InnerProductSpace.toDual ℝ (PrimalSpace B))
            ((InnerProductSpace.toDual ℝ (PrimalSpace B)).symm
              (fderiv ℝ (fderiv ℝ f) x d)) u := by
              simp
    _ = (InnerProductSpace.toDual ℝ (PrimalSpace B))
          (strongDualToPrimalMap (fderiv ℝ (fderiv ℝ f) x d)) u := by
          rw [hD]
    _ = (InnerProductSpace.toDual ℝ (PrimalSpace B)) (hessian f x d) u := by
          rw [happly]
    _ = ((primalToStrongDualMap.comp (hessian f x)) d) u := by
          rfl

omit [Fact B.toQuadraticMap.PosDef] in
/-- Helper for Lemma 4.3.3: evaluating the operator-level Riesz bridge recovers the Hessian
covector as the applied second Fréchet derivative. -/
private lemma hessianCovector_eq_sndFDeriv_apply
    {x d : PrimalSpace B} (hcont : ContDiffAt ℝ 2 f x) :
    (InnerProductSpace.toDual ℝ (PrimalSpace B)) (hessian f x d) =
      fderiv ℝ (fderiv ℝ f) x d := by
  -- Reuse the operator bridge and evaluate it on the displacement direction `d`.
  simpa [ContinuousLinearMap.comp_apply] using
    congrArg (fun T => T d)
      (sndFDeriv_eq_toDual_comp_hessian_onPrimalSpace (f := f) hcont).symm

/-- Helper for Lemma 4.3.3: after transporting the Hessian term through
`InnerProductSpace.toDual ℝ (PrimalSpace B)`, the shifted covector is exactly the first-order
Taylor remainder of `fderiv ℝ f`. -/
private lemma associatedShiftEqFderivRemainder
    {M : ℝ} (step : CubicNewtonStep B f M) (x : PrimalSpace B)
    (hcont : ContDiffAt ℝ 2 f x) :
    (fderiv ℝ f (step x) : PrimalSpace B →L[ℝ] ℝ) +
        (((M / 2 : ℝ) * r[step](x)) •
          bilinCovector (B.toQuadraticMap.associated) (step x - x)) =
      fderiv ℝ f (step x) - fderiv ℝ f x -
        fderiv ℝ (fderiv ℝ f) x (step x - x) := by
  let d : PrimalSpace B := step x - x
  have hSymm :
      BilinForm.IsSymm (B.toQuadraticMap.associated : BilinForm ℝ (PrimalSpace B)) := by
    -- The associated bilinear form is symmetric by construction.
    exact ⟨QuadraticMap.associated_isSymm ℝ B.toQuadraticMap⟩
  have hgrad :
      (InnerProductSpace.toDual ℝ (PrimalSpace B)) (∇ f x) = fderiv ℝ f x :=
    gradientCovector_eq_fderivAt (f := f) hcont
  have hhess :
      (InnerProductSpace.toDual ℝ (PrimalSpace B)) (hessian f x d) =
        fderiv ℝ (fderiv ℝ f) x d :=
    hessianCovector_eq_sndFDeriv_apply (f := f) (d := d) hcont
  have hopt :
      (InnerProductSpace.toDual ℝ (PrimalSpace B)) (∇ f x + hessian f x d) +
          (((M / 2 : ℝ) * r[step](x)) •
            bilinCovector (B.toQuadraticMap.associated) d) = 0 := by
    -- Stay on `PrimalSpace B` and import only the associated-form optimality identity.
    simpa [d, bilinCovector, associatedStepResidualNormEq step x] using
      CubicNewtonStep.firstOrderOptimalityCondition_toDual
        (B := B.toQuadraticMap.associated) (f := f) (M := M)
        (step := associated_cubicNewtonStep step) (x := x) hSymm hcont
  have hopt' :
      fderiv ℝ f x + fderiv ℝ (fderiv ℝ f) x d +
          (((M / 2 : ℝ) * r[step](x)) •
            bilinCovector (B.toQuadraticMap.associated) d) = 0 := by
    -- Convert the associated optimality equation from gradients/Hessians to `fderiv`.
    simpa [map_add, hgrad, hhess] using hopt
  have hshift :
      (((M / 2 : ℝ) * r[step](x)) •
          bilinCovector (B.toQuadraticMap.associated) d) =
        -(fderiv ℝ f x + fderiv ℝ (fderiv ℝ f) x d) := by
    -- Solve the stationarity identity for the explicit associated covector shift.
    exact eq_neg_of_add_eq_zero_right hopt'
  -- Add `fderiv ℝ f (step x)` to the solved stationarity relation and flatten the additive form.
  calc
    (fderiv ℝ f (step x) : PrimalSpace B →L[ℝ] ℝ) +
        (((M / 2 : ℝ) * r[step](x)) • bilinCovector (B.toQuadraticMap.associated) d)
      = fderiv ℝ f (step x) + (-(fderiv ℝ f x + fderiv ℝ (fderiv ℝ f) x d)) := by
          rw [hshift]
    _ = fderiv ℝ f (step x) - fderiv ℝ f x - fderiv ℝ (fderiv ℝ f) x d := by
          abel_nf

/-- Helper for Lemma 4.3.3: the first-order Taylor remainder of `fderiv ℝ f` on `PrimalSpace B`
is bounded by `((Mf : ℝ) / 2) * ‖y - x‖^2`. -/
private lemma fderivDeviation_le
    (hf :
      letI : NormedAddCommGroup (PrimalSpace B) :=
        LinearMap.BilinForm.instNormedAddCommGroupPrimalSpaceOfFactPosDefRealToQuadraticMap B
      letI : NormedSpace ℝ (PrimalSpace B) :=
        LinearMap.BilinForm.instNormedSpaceRealPrimalSpace B
      (f : PrimalSpace B → ℝ) ∈ C22[(Mf : NNReal)])
    (x y : PrimalSpace B) :
    ‖fderiv ℝ f y - fderiv ℝ f x - fderiv ℝ (fderiv ℝ f) x (y - x)‖[B,*] ≤
      ((Mf : ℝ) / 2) * ‖y - x‖[B] ^ (2 : ℕ) := by
  letI : NormedAddCommGroup (PrimalSpace B) :=
    LinearMap.BilinForm.instNormedAddCommGroupPrimalSpaceOfFactPosDefRealToQuadraticMap B
  letI : NormedSpace ℝ (PrimalSpace B) :=
    LinearMap.BilinForm.instNormedSpaceRealPrimalSpace B
  let remainder : PrimalSpace B →L[ℝ] ℝ :=
    fderiv ℝ f y - fderiv ℝ f x - fderiv ℝ (fderiv ℝ f) x (y - x)
  have hresult :
      ‖remainder‖[B,*] ≤ ((Mf : ℝ) / 2) * ‖y - x‖[B] ^ (2 : ℕ) := by
    have hgeneric :
        ‖remainder‖ ≤ ((Mf : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
      exact
        HasLipschitzContinuousHessian.fderivRemainderNorm_le
          (L3 := Mf) (g := f) hf x y
    have hnorm :
        ‖remainder‖[B,*] = ‖remainder‖ := by
      symm
      simpa [remainder] using
        LinearMap.BilinForm.strongDualNorm_eq_bDualNormOnPrimalSpace
          (B := B) remainder
    -- Transport the ambient operator norm to the chapter `B`-dual norm only once.
    calc
      ‖remainder‖[B,*] = ‖remainder‖ := hnorm
      _ ≤ ((Mf : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := hgeneric
      _ = ((Mf : ℝ) / 2) * ‖y - x‖[B] ^ (2 : ℕ) := by
            rw [← LinearMap.BilinForm.primalSpace_norm_eq_bInducedNorm (B := B) (x := y - x)]
  simpa [remainder] using hresult

/-- Helper for Lemma 4.3.3: after rewriting the shifted covector to the gradient remainder, the
associated dual norm is bounded by the Chapter 1 quadratic Taylor remainder. -/
private lemma associatedDualShiftBoundAtResidual
    (hf :
      letI : NormedAddCommGroup (PrimalSpace B) :=
        LinearMap.BilinForm.instNormedAddCommGroupPrimalSpaceOfFactPosDefRealToQuadraticMap B
      letI : NormedSpace ℝ (PrimalSpace B) :=
        LinearMap.BilinForm.instNormedSpaceRealPrimalSpace B
      (f : PrimalSpace B → ℝ) ∈ C22[(Mf : NNReal)])
    {M : ℝ} (step : CubicNewtonStep B f M) (x : PrimalSpace B)
    [Fact (B.toQuadraticMap.associated).toQuadraticMap.PosDef] :
    ‖(fderiv ℝ f (step x) : PrimalSpace B →L[ℝ] ℝ) +
        (((M / 2 : ℝ) * r[step](x)) •
          bilinCovector (B.toQuadraticMap.associated) (step x - x))‖[B.toQuadraticMap.associated,*]
      ≤
      ((Mf : ℝ) / 2) * (r[step](x)) ^ (2 : ℕ) := by
  have hcont : ContDiffAt ℝ 2 f x := by
    letI : NormedAddCommGroup (PrimalSpace B) :=
      LinearMap.BilinForm.instNormedAddCommGroupPrimalSpaceOfFactPosDefRealToQuadraticMap B
    letI : NormedSpace ℝ (PrimalSpace B) :=
      LinearMap.BilinForm.instNormedSpaceRealPrimalSpace B
    simpa using (hf.contDiff.contDiffAt (x := x))
  have hbound := fderivDeviation_le (hf := hf) x (step x)
  -- Rewrite the shifted associated covector to the derivative remainder and convert the dual norm
  -- only once at the end.
  calc
    ‖(fderiv ℝ f (step x) : PrimalSpace B →L[ℝ] ℝ) +
        (((M / 2 : ℝ) * r[step](x)) •
          bilinCovector (B.toQuadraticMap.associated) (step x - x))‖[B.toQuadraticMap.associated,*]
      = ‖fderiv ℝ f (step x) - fderiv ℝ f x -
          fderiv ℝ (fderiv ℝ f) x (step x - x)‖[B.toQuadraticMap.associated,*] := by
            rw [associatedShiftEqFderivRemainder (f := f) (step := step) (x := x) hcont]
    _ = ‖fderiv ℝ f (step x) - fderiv ℝ f x -
          fderiv ℝ (fderiv ℝ f) x (step x - x)‖[B,*] := by
            rw [associatedDualNormEqOnPrimalSpace]
    _ ≤ ((Mf : ℝ) / 2) * (r[step](x)) ^ (2 : ℕ) := by
            simpa [CubicNewtonStep.residual_apply]
              using hbound

/-- Helper for Lemma 4.3.3: if a radius parameter `ρ` is already fixed to equal `‖d‖[A]`, then
the generic dual-shift lower bound can be consumed without re-normalizing the whole conclusion. -/
private lemma dual_pairing_lower_bound_of_dual_shift_bound_radius
    {A : BilinForm ℝ E} [Fact A.toQuadraticMap.PosDef]
    (hSymm : A.IsSymm) {M Mf ρ : ℝ} (hM : 0 < M)
    (d : E) (g : E →L[ℝ] ℝ)
    (hρ : ρ = ‖d‖[A])
    (hshift :
      ‖g + (((M / 2 : ℝ) * ρ) • bilinCovector A d)‖[A,*] ≤
        ((Mf : ℝ) / 2) * ρ ^ (2 : ℕ)) :
    g (-d) ≥
      (1 / (M * ρ)) * ‖g‖[A,*] ^ (2 : ℕ) +
        ((M ^ (2 : ℕ) - Mf ^ (2 : ℕ)) / (4 * M)) * ρ ^ (3 : ℕ) := by
  -- Replace the fixed radius parameter by the geometric norm once, then invoke the generic engine.
  subst ρ
  simpa using
    dual_pairing_lower_bound_of_dual_shift_bound hSymm hM d g hshift

/-- Helper for Lemma 4.3.3: on the associated symmetric surface, the gradient pairing lower bound
already closes in residual spelling `r[step](x)` without reverting to the pointwise norm form. -/
private lemma associatedDualPairingLowerBoundAtResidual
    (hf :
      letI : NormedAddCommGroup (PrimalSpace B) :=
        LinearMap.BilinForm.instNormedAddCommGroupPrimalSpaceOfFactPosDefRealToQuadraticMap B
      letI : NormedSpace ℝ (PrimalSpace B) :=
        LinearMap.BilinForm.instNormedSpaceRealPrimalSpace B
      (f : PrimalSpace B → ℝ) ∈ C22[(Mf : NNReal)])
    {M : ℝ} (step : CubicNewtonStep B f M) (hM : 0 < M) (x : PrimalSpace B) :
    let g : PrimalSpace B →L[ℝ] ℝ := fderiv ℝ f (step x)
    let d : PrimalSpace B := step x - x
    g (-d) ≥
      (1 / (M * r[step](x))) * ‖g‖[B.toQuadraticMap.associated,*] ^ (2 : ℕ) +
        ((M ^ (2 : ℕ) - (Mf : ℝ) ^ (2 : ℕ)) / (4 * M)) * (r[step](x)) ^ (3 : ℕ) := by
  let g : PrimalSpace B →L[ℝ] ℝ := fderiv ℝ f (step x)
  let d : PrimalSpace B := step x - x
  have hSymm : BilinForm.IsSymm (B.toQuadraticMap.associated : BilinForm ℝ (PrimalSpace B)) := by
    -- The associated surface is symmetric by construction.
    exact ⟨QuadraticMap.associated_isSymm ℝ B.toQuadraticMap⟩
  have hρ : r[step](x) = ‖d‖[B.toQuadraticMap.associated] := by
    -- Keep the residual parameter fixed and rewrite only the displacement norm.
    simpa [d] using
      (associatedStepResidualNormEq step x).symm
  have hshift :
      ‖g + (((M / 2 : ℝ) * r[step](x)) •
          bilinCovector (B.toQuadraticMap.associated) d)‖[B.toQuadraticMap.associated,*] ≤
        ((Mf : ℝ) / 2) * (r[step](x)) ^ (2 : ℕ) := by
    -- Consume the Taylor remainder estimate in the same residual spelling.
    simpa [g, d] using
      associatedDualShiftBoundAtResidual hf step x
  -- Route correction: feed the residual-spelled bound directly to the algebraic engine.
  exact
    dual_pairing_lower_bound_of_dual_shift_bound_radius hSymm hM d g hρ hshift

/-- Helper for Lemma 4.3.3: on `PrimalSpace B`, the associated-form lower bound only needs the
displacement rewrite `x - step x = -(step x - x)` before the final dual-norm transport. -/
private lemma cubicNewtonStep_dualPairing_lower_boundOnPrimalSpaceAssociated
    (hf :
      letI : NormedAddCommGroup (PrimalSpace B) :=
        LinearMap.BilinForm.instNormedAddCommGroupPrimalSpaceOfFactPosDefRealToQuadraticMap B
      letI : NormedSpace ℝ (PrimalSpace B) :=
        LinearMap.BilinForm.instNormedSpaceRealPrimalSpace B
      (f : PrimalSpace B → ℝ) ∈ C22[(Mf : NNReal)])
    {M : ℝ} (step : CubicNewtonStep B f M)
    (hM : 0 < M)
    (x : PrimalSpace B) :
    (fderiv ℝ f (step x)) (x - step x) ≥
      (1 / (M * r[step](x))) *
          ‖fderiv ℝ f (step x)‖[B.toQuadraticMap.associated,*] ^ (2 : ℕ) +
        ((M ^ (2 : ℕ) - (Mf : ℝ) ^ (2 : ℕ)) / (4 * M)) *
          (r[step](x)) ^ (3 : ℕ) := by
  let g : PrimalSpace B →L[ℝ] ℝ := fderiv ℝ f (step x)
  let d : PrimalSpace B := step x - x
  have hbound :
      g (-d) ≥
        (1 / (M * r[step](x))) * ‖g‖[B.toQuadraticMap.associated,*] ^ (2 : ℕ) +
          ((M ^ (2 : ℕ) - (Mf : ℝ) ^ (2 : ℕ)) / (4 * M)) * (r[step](x)) ^ (3 : ℕ) := by
    -- Use the residual-spelled associated theorem without introducing a second norm spelling.
    simpa [g, d] using
      associatedDualPairingLowerBoundAtResidual hf step hM x
  have hdisp : x - step x = -d := by
    -- Normalize the displacement once before the final lower-bound application.
    dsimp [d]
    abel
  calc
    (fderiv ℝ f (step x)) (x - step x) = g (x - step x) := by
      rfl
    _ = g (-d) := by
      rw [hdisp]
    _ ≥
        (1 / (M * r[step](x))) * ‖g‖[B.toQuadraticMap.associated,*] ^ (2 : ℕ) +
          ((M ^ (2 : ℕ) - (Mf : ℝ) ^ (2 : ℕ)) / (4 * M)) * (r[step](x)) ^ (3 : ℕ) := hbound

/-- Helper for Lemma 4.3.3: the first lower bound on the gradient pairing is easiest to prove on
the intrinsic carrier `PrimalSpace B`, where the `B`-geometry is the ambient norm. -/
lemma cubicNewtonStep_dualPairing_lower_boundOnPrimalSpace
    (hf :
      letI : NormedAddCommGroup (PrimalSpace B) :=
        LinearMap.BilinForm.instNormedAddCommGroupPrimalSpaceOfFactPosDefRealToQuadraticMap B
      letI : NormedSpace ℝ (PrimalSpace B) :=
        LinearMap.BilinForm.instNormedSpaceRealPrimalSpace B
      (f : PrimalSpace B → ℝ) ∈ C22[(Mf : NNReal)])
    {M : ℝ} (step : CubicNewtonStep B f M)
    (hM : 0 < M)
    (x : PrimalSpace B) :
    (fderiv ℝ f (step x)) (x - step x) ≥
      (1 / (M * r[step](x))) *
          ‖fderiv ℝ f (step x)‖[B,*] ^ (2 : ℕ) +
        ((M ^ (2 : ℕ) - (Mf : ℝ) ^ (2 : ℕ)) / (4 * M)) *
          (r[step](x)) ^ (3 : ℕ) := by
  have hassociated :
      (fderiv ℝ f (step x)) (x - step x) ≥
        (1 / (M * r[step](x))) *
            ‖fderiv ℝ f (step x)‖[B.toQuadraticMap.associated,*] ^ (2 : ℕ) +
          ((M ^ (2 : ℕ) - (Mf : ℝ) ^ (2 : ℕ)) / (4 * M)) * (r[step](x)) ^ (3 : ℕ) := by
    -- First close the theorem in the associated dual norm.
    exact
      cubicNewtonStep_dualPairing_lower_boundOnPrimalSpaceAssociated
        hf step hM x
  -- Then rewrite only the dual norm back to the source `B` spelling.
  simpa [associatedDualNormEqOnPrimalSpace (fderiv ℝ f (step x))] using hassociated

/-- Lemma 4.3.3 (1): the pairing of the gradient at the cubic Newton point with the displacement
`x - T_M(x)` is bounded below by the reciprocal-residual dual-gradient term plus the cubic
correction `((M² - M_f²) / (4M)) r_M(x)^3`. -/
lemma cubicNewtonStep_dualPairing_lower_bound
    (hf :
      letI : NormedAddCommGroup (PrimalSpace B) :=
        LinearMap.BilinForm.instNormedAddCommGroupPrimalSpaceOfFactPosDefRealToQuadraticMap B
      letI : NormedSpace ℝ (PrimalSpace B) :=
        LinearMap.BilinForm.instNormedSpaceRealPrimalSpace B
      (f : PrimalSpace B → ℝ) ∈ C22[(Mf : NNReal)])
    {M : ℝ} (step : CubicNewtonStep B f M)
    (hM : 0 < M)
    (x : PrimalSpace B) :
    let g := fderiv ℝ f (step x)
    g (x - step x) ≥
      (1 / (M * r[step](x))) *
          ‖g‖[B,*] ^ (2 : ℕ) +
        ((M ^ (2 : ℕ) - (Mf : ℝ) ^ (2 : ℕ)) / (4 * M)) *
          (r[step](x)) ^ (3 : ℕ) := by
  -- This is exactly the intrinsic `PrimalSpace B` lower bound already proved above.
  simpa using cubicNewtonStep_dualPairing_lower_boundOnPrimalSpace hf step hM x

-- Proof sketch: start from `cubicNewtonStep_dualPairing_lower_bound`, use the hypothesis
-- `M ≥ M_f / σ` in the equivalent form `M_f ≤ σ M`, and simplify the cubic coefficient
-- `((M² - M_f²) / (4M))` to `((1 - σ²) / 4) M`.
/-- Lemma 4.3.3 (2): if `σ ∈ (0, 1]` and `M ≥ M_f / σ`, then the cubic correction in the lower
bound can be replaced by `((1 - σ²) / 4) M r_M(x)^3`. -/
lemma cubicNewtonStep_dualPairing_lower_bound_of_sigma
    (hf :
      letI : NormedAddCommGroup (PrimalSpace B) :=
        LinearMap.BilinForm.instNormedAddCommGroupPrimalSpaceOfFactPosDefRealToQuadraticMap B
      letI : NormedSpace ℝ (PrimalSpace B) :=
        LinearMap.BilinForm.instNormedSpaceRealPrimalSpace B
      (f : PrimalSpace B → ℝ) ∈ C22[(Mf : NNReal)])
    {M : ℝ} (step : CubicNewtonStep B f M)
    (hM : 0 < M)
    {σ : ℝ}
    (hσ : σ ∈ Set.Ioc (0 : ℝ) 1)
    (hMσ : M ≥ (1 / σ) * (Mf : ℝ))
    (x : PrimalSpace B) :
    let g := fderiv ℝ f (step x)
    g (x - step x) ≥
      (1 / (M * r[step](x))) *
          ‖g‖[B,*] ^ (2 : ℕ) +
        ((1 - σ ^ (2 : ℕ)) / 4 : ℝ) * M * (r[step](x)) ^ (3 : ℕ) := by
  have hbase := cubicNewtonStep_dualPairing_lower_bound hf step hM x
  have hcoeff :
      ((1 - σ ^ (2 : ℕ)) / 4 : ℝ) * M ≤
        (M ^ (2 : ℕ) - (Mf : ℝ) ^ (2 : ℕ)) / (4 * M) :=
    sigma_cubic_coefficient_lower_bound (Mf := Mf) hσ hMσ hM
  -- Replace the cubic coefficient by the smaller sigma-dependent one.
  dsimp at hbase ⊢
  have hrad : 0 ≤ r[step](x) := by
    rw [CubicNewtonStep.residual_apply]
    exact Real.sqrt_nonneg _
  have hrad_nonneg : 0 ≤ (r[step](x)) ^ (3 : ℕ) := by
    exact pow_nonneg hrad 3
  have hterm :
      (1 / (M * r[step](x))) * ‖fderiv ℝ f (step x)‖[B,*] ^ (2 : ℕ) +
          ((1 - σ ^ (2 : ℕ)) / 4 : ℝ) * M * (r[step](x)) ^ (3 : ℕ)
        ≤
        (1 / (M * r[step](x))) * ‖fderiv ℝ f (step x)‖[B,*] ^ (2 : ℕ) +
          ((M ^ (2 : ℕ) - (Mf : ℝ) ^ (2 : ℕ)) / (4 * M)) * (r[step](x)) ^ (3 : ℕ) := by
    gcongr
  exact hterm.trans hbase

end
