/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_6_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
  [NormedAddCommGroup E₃] [InnerProductSpace ℝ E₃] [CompleteSpace E₃]

noncomputable local instance instLocalChap05_Theorem_5_4_6_71 : SeminormedAddCommGroup (E₂ × E₃) :=
  WithLp.seminormedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instLocalChap05_Theorem_5_4_6_72 : NormedAddCommGroup (E₂ × E₃) :=
  WithLp.normedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instLocalChap05_Theorem_5_4_6_73 : NormedSpace ℝ (E₂ × E₃) :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instInnerProductSpaceChap05_Theorem_5_4_6_71 : InnerProductSpace ℝ (E₂ × E₃) where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 E₂ E₃ x]
    exact InnerProductSpace.norm_sq_eq_re_inner (WithLp.toLp 2 x)
  conj_inner_symm x y := by
    change inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 x) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_comm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  add_left x y z := by
    change inner ℝ (WithLp.toLp 2 x + WithLp.toLp 2 y) (WithLp.toLp 2 z) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 z) +
        inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 z)
    simpa using inner_add_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) (WithLp.toLp 2 z)
  smul_left x y r := by
    change inner ℝ (r • WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      r * inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_smul_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) r

noncomputable local instance instLocalChap05_Theorem_5_4_6_74 : CompleteSpace (E₂ × E₃) := inferInstance

/- Theorem 5.4.6.7 lies in the chapter's composed third-order directional-differentiation domain.

Sampled owner declarations:
* `thirdDirectionalDerivative` from `Definition_5_0_10`, the chapter owner for scalar repeated
  third directional derivatives;
* `vectorThirdDirectionalDerivative` from `Definition_5_4_6_2`, the chapter owner for
  `D³ξ(x)[d, d, d]`;
* `hessian` from `Chap01/Definition_1_4_16`, the canonical owner for the mixed second-order term;
* `compositionPotential` from `Definition_5_4_6_6` together with
  `compositionSecondLiftedDirectionDerivative` from `Definition_5_4_6_7`, the subsection's
  source-facing composition owners.

Source/core/bridge triage:
* source-facing: the decomposition `(5.4.25)` for the third directional derivative of
  `ψ(x, z) = Φ(ξ(x), z)`;
* core/canonical: `thirdDirectionalDerivative`, `hessian`, and
  `vectorThirdDirectionalDerivative`;
* bridge/view: the canonical lifted pair `(fderiv ℝ ξ x d, 0)` and
  `compositionSecondLiftedDirectionDerivative`.

Primitive data:
* `Φ`, `ξ`, `x`, `z`, `d`.

Derived API:
* the third directional derivative of the fixed-`z` composition;
* the lifted direction `l = (Dξ(x)[d], 0)`;
* the derivative `l' = Dl(x)[d]`;
* the gradient pairing with `D³ξ(x)[d, d, d]`.

The theorem surface should therefore use the existing owner vocabulary for all three summands:
`thirdDirectionalDerivative Φ (ξ x, z) l`, the mixed Hessian pairing with the lifted derivative
`compositionSecondLiftedDirectionDerivative ξ x d`, and the final pairing with
`vectorThirdDirectionalDerivative ξ x d`, instead of exposing parallel raw `iteratedFDeriv` and
raw `fderiv` spellings. -/

-- Proof sketch: differentiate the second-derivative decomposition from
-- `compositionPotential_secondDirectionalDerivative_eq_sigmaOne_add_sigmaTwo` once more along the
-- repeated direction `d`. The chain rule gives the third derivative of `Φ` in the lifted
-- direction `l = (Dξ(x)[d], 0)`, differentiating the Hessian quadratic form contributes the
-- coefficient `3` in front of the mixed Hessian pairing with `l' = (D²ξ(x)[d, d], 0)`, and the
-- remaining term is the pairing of the `y`-gradient of `Φ` with `D³ξ(x)[d, d, d]`.
/-- Helper for Theorem 5.4.6.7: the affine line `t ↦ x + t • d` has derivative `d`. -/
private lemma affine_line_hasDerivAt
    (x d : E₁) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate scalar multiplication first and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

/-- Helper for Theorem 5.4.6.7: the affine line has vanishing second iterated derivative. -/
private lemma affine_line_iteratedDeriv_two
    {x d : E₁} :
    iteratedDeriv 2 (fun s : ℝ ↦ x + s • d) = fun _ : ℝ ↦ (0 : E₁) := by
  -- Differentiate the affine line once to a constant, then differentiate that constant again.
  ext t
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv : deriv (fun s : ℝ ↦ x + s • d) = fun _ : ℝ ↦ d := by
    ext s
    exact (affine_line_hasDerivAt x d s).deriv
  rw [hderiv, deriv_const]

/-- Helper for Theorem 5.4.6.7: the affine line has vanishing third iterated derivative. -/
private lemma affine_line_iteratedDeriv_three
    {x d : E₁} :
    iteratedDeriv 3 (fun s : ℝ ↦ x + s • d) = fun _ : ℝ ↦ (0 : E₁) := by
  -- Once the second iterated derivative is identically zero, one more derivative stays zero.
  ext t
  rw [iteratedDeriv_succ, affine_line_iteratedDeriv_two, deriv_const]

omit [CompleteSpace E₂] in
/-- Helper for Theorem 5.4.6.7: the second iterated derivative of the source line slice of `ξ`
is `D²ξ(x)[d, d]`. -/
private lemma line_slice_iteratedDeriv_two_eq_vectorSecondDirectionalDerivative
    {ξ : E₁ → E₂} {x d : E₁}
    (hξ : ContDiffAt ℝ 3 ξ x) :
    iteratedDeriv 2 (fun s : ℝ ↦ ξ (x + s • d)) 0 =
      vectorSecondDirectionalDerivative ξ x d := by
  let line : ℝ → E₁ := fun s ↦ x + s • d
  have hξ₂ : ContDiffAt ℝ 2 ξ x := hξ.of_le (by norm_num)
  have hline₂ : ContDiffAt ℝ 2 line 0 := by
    fun_prop
  -- The quadratic Faà di Bruno formula collapses because the affine line has zero second
  -- iterated derivative.
  have hcomp :=
    iteratedDeriv_vcomp_two (by simpa [line] using hξ₂) hline₂
  have hline_deriv : deriv line 0 = d := by
    simpa [line] using (affine_line_hasDerivAt x d 0).deriv
  simpa [line, Function.comp, hline_deriv, affine_line_iteratedDeriv_two,
    vectorSecondDirectionalDerivative] using hcomp

omit [CompleteSpace E₂] in
/-- Helper for Theorem 5.4.6.7: the third iterated derivative of the source line slice of `ξ`
is `D³ξ(x)[d, d, d]`. -/
private lemma line_slice_iteratedDeriv_three_eq_vectorThirdDirectionalDerivative
    {ξ : E₁ → E₂} {x d : E₁}
    (hξ : ContDiffAt ℝ 3 ξ x) :
    iteratedDeriv 3 (fun s : ℝ ↦ ξ (x + s • d)) 0 =
      vectorThirdDirectionalDerivative ξ x d := by
  let line : ℝ → E₁ := fun s ↦ x + s • d
  have hline₃ : ContDiffAt ℝ 3 line 0 := by
    fun_prop
  -- The cubic Faà di Bruno formula reduces to the pure third derivative term because every
  -- higher derivative of the affine line vanishes.
  have hcomp :=
    iteratedDeriv_vcomp_three (by simpa [line] using hξ) hline₃
  have hline_deriv : deriv line 0 = d := by
    simpa [line] using (affine_line_hasDerivAt x d 0).deriv
  have hzero_left : iteratedFDeriv ℝ 2 ξ x ![(0 : E₁), d] = 0 := by
    exact (iteratedFDeriv ℝ 2 ξ x).map_coord_zero 0 rfl
  have hzero_right : iteratedFDeriv ℝ 2 ξ x ![d, (0 : E₁)] = 0 := by
    exact (iteratedFDeriv ℝ 2 ξ x).map_coord_zero 1 rfl
  calc
    iteratedDeriv 3 (fun s : ℝ ↦ ξ (x + s • d)) 0
      = iteratedFDeriv ℝ 3 ξ x (fun _ ↦ d) +
          iteratedFDeriv ℝ 2 ξ x ![(0 : E₁), d] +
          2 • iteratedFDeriv ℝ 2 ξ x ![d, (0 : E₁)] := by
            simpa [line, Function.comp, hline_deriv, affine_line_iteratedDeriv_two,
              affine_line_iteratedDeriv_three] using hcomp
    _ = vectorThirdDirectionalDerivative ξ x d := by
          simp [hzero_left, hzero_right, vectorThirdDirectionalDerivative]

/-- Helper for Theorem 5.4.6.7: the second iterated Fréchet derivative of a scalar field on the
ambient product space is the Hessian pairing. -/
private lemma ambient_iteratedFDeriv_two_eq_hessian_pairing
    {Φ : E₂ × E₃ → ℝ} {p u v : E₂ × E₃}
    (hΦ : ContDiffAt ℝ 2 Φ p) :
    iteratedFDeriv ℝ 2 Φ p ![u, v] = inner ℝ (hessian Φ p u) v := by
  -- Rewrite the Hessian through the derivative of the gradient and identify the resulting
  -- bilinear pairing with the second iterated Fréchet derivative.
  symm
  let D : StrongDual ℝ (E₂ × E₃) ≃L[ℝ] E₂ × E₃ :=
    (InnerProductSpace.toDual ℝ (E₂ × E₃)).symm.toContinuousLinearEquiv
  let Dclm : StrongDual ℝ (E₂ × E₃) →L[ℝ] E₂ × E₃ := D.toContinuousLinearMap
  have hΦfderiv_C1 : ContDiffAt ℝ 1 (fderiv ℝ Φ) p := by
    exact hΦ.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hΦfderiv_diff : DifferentiableAt ℝ (fderiv ℝ Φ) p := by
    exact hΦfderiv_C1.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hD_hasFDeriv : HasFDerivAt (fun y : StrongDual ℝ (E₂ × E₃) ↦ D y) Dclm
      (fderiv ℝ Φ p) :=
    Dclm.hasFDerivAt
  have hgrad_hasFDeriv :
      HasFDerivAt (∇ Φ) (Dclm.comp (fderiv ℝ (fderiv ℝ Φ) p)) p := by
    -- Rewrite the gradient as the Riesz representation of the Fréchet derivative.
    simpa [D, Dclm, gradient] using hD_hasFDeriv.comp p hΦfderiv_diff.hasFDerivAt
  let y : StrongDual ℝ (E₂ × E₃) := (fderiv ℝ (fderiv ℝ Φ) p) u
  have hRiesz : inner ℝ (D y) v = y v := InnerProductSpace.toDual_symm_apply
  rw [hessian, hgrad_hasFDeriv.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  calc
    inner ℝ (D ((fderiv ℝ (fderiv ℝ Φ) p) u)) v = ((fderiv ℝ (fderiv ℝ Φ) p) u) v := by
      change inner ℝ (D y) v = y v
      exact hRiesz
    _ = iteratedFDeriv ℝ 2 Φ p ![u, v] := by
      simp [iteratedFDeriv_two_apply]

omit [CompleteSpace E₂] [CompleteSpace E₃] in
/-- Helper for Theorem 5.4.6.7: the ambient second iterated Fréchet derivative is symmetric in
its ordered slots. -/
private lemma ambient_iteratedFDeriv_two_swap_at
    {Φ : E₂ × E₃ → ℝ} {p u v : E₂ × E₃}
    (hΦ : ContDiffAt ℝ 2 Φ p) :
    iteratedFDeriv ℝ 2 Φ p ![u, v] = iteratedFDeriv ℝ 2 Φ p ![v, u] := by
  -- Use the standard symmetry of the second Fréchet derivative over `ℝ`.
  have hsymm : IsSymmSndFDerivAt ℝ Φ p := hΦ.isSymmSndFDerivAt (by norm_num)
  simpa using hsymm.iteratedFDeriv_cons

/-- Helper for Theorem 5.4.6.7: the derivative of the fixed-`z` lifted line is the lifted
direction `(Dξ(x)[d], 0)`. -/
private lemma liftedFixedZLineDerivEq
    {ξ : E₁ → E₂} {x d : E₁} {z : E₃}
    (hξ : ContDiffAt ℝ 3 ξ x) :
    deriv (fun s : ℝ ↦ (ξ (x + s • d), z)) 0 = (fderiv ℝ ξ x d, (0 : E₃)) := by
  have hline : HasDerivAt (fun s : ℝ ↦ x + s • d) d 0 := by
    -- The affine source line contributes the repeated direction `d`.
    simpa using affine_line_hasDerivAt x d 0
  have hξdiff : DifferentiableAt ℝ ξ x := hξ.differentiableAt (by norm_num)
  have hleft :
      HasDerivAt (fun s : ℝ ↦ ξ (x + s • d)) (fderiv ℝ ξ x d) 0 := by
    -- Compose the derivative of `ξ` at `x` with the derivative of the affine line at `0`.
    simpa using hξdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hlifted :
      HasDerivAt (fun s : ℝ ↦ (ξ (x + s • d), z)) (fderiv ℝ ξ x d, (0 : E₃)) 0 := by
    -- The second component is constant, so only the horizontal derivative survives.
    exact hleft.prodMk (hasDerivAt_const (0 : ℝ) z)
  exact hlifted.deriv

/-- Helper for Theorem 5.4.6.7: the second iterated derivative of the fixed-`z` lifted line is
`(D²ξ(x)[d, d], 0)`. -/
private lemma liftedFixedZLineSecondIteratedDerivEq
    {ξ : E₁ → E₂} {x d : E₁} {z : E₃}
    (hξ : ContDiffAt ℝ 3 ξ x) :
    iteratedDeriv 2 (fun s : ℝ ↦ (ξ (x + s • d), z)) 0 =
      compositionSecondLiftedDirectionDerivative ξ x d := by
  let lifted : E₁ → E₂ × E₃ := fun y ↦ (ξ y, z)
  have hlifted : ContDiffAt ℝ 3 lifted x := by
    -- Lift `ξ` to the fixed-`z` pair map before invoking the line-slice chain rule.
    let liftedLp : E₁ → WithLp 2 (E₂ × E₃) := fun y ↦ WithLp.toLp 2 (ξ y, z)
    have hliftedLp : ContDiffAt ℝ 3 liftedLp x := by
      letI : SeminormedAddCommGroup (E₂ × E₃) := Prod.seminormedAddCommGroup
      letI : NormedAddCommGroup (E₂ × E₃) := Prod.normedAddCommGroup
      letI : NormedSpace ℝ (E₂ × E₃) := Prod.normedSpace
      have hpairStd : ContDiffAt ℝ 3 (fun y : E₁ ↦ (ξ y, z)) x := by
        exact hξ.prodMk (contDiffAt_const : ContDiffAt ℝ 3 (fun _ : E₁ ↦ z) x)
      have htoLp :
          ContDiffAt ℝ 3 (fun p : E₂ × E₃ ↦ WithLp.toLp 2 p) (ξ x, z) := by
        simpa [WithLp.prodContinuousLinearEquiv_symm_apply] using
          ((WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃).symm.toContinuousLinearMap.contDiff.contDiffAt :
            ContDiffAt ℝ 3
              ((WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃).symm.toContinuousLinearMap)
              (ξ x, z))
      simpa [liftedLp] using htoLp.comp x hpairStd
    have hofLp :
        ContDiffAt ℝ 3
          (fun w : WithLp 2 (E₂ × E₃) ↦ (WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃) w)
          (liftedLp x) := by
      simpa using
        ((WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃).toContinuousLinearMap.contDiff.contDiffAt :
          ContDiffAt ℝ 3
            ((WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃).toContinuousLinearMap)
            (liftedLp x))
    simpa [lifted, liftedLp] using hofLp.comp x hliftedLp
  calc
    iteratedDeriv 2 (fun s : ℝ ↦ (ξ (x + s • d), z)) 0
      = vectorSecondDirectionalDerivative lifted x d := by
          -- The pair-valued line slice is the standard line slice of the lifted map.
          simpa [lifted] using
            line_slice_iteratedDeriv_two_eq_vectorSecondDirectionalDerivative
              (ξ := lifted) (x := x) (d := d) hlifted
    _ = compositionSecondLiftedDirectionDerivative ξ x d := by
          -- Compare the pair-valued second Fréchet derivative through the two coordinate
          -- projections; the constant `z` branch contributes zero.
          ext
          · have hfst :=
              congrArg
                (fun M : E₁ [×2]→L[ℝ] E₂ => M (fun _ ↦ d))
                ((ContinuousLinearMap.fst ℝ E₂ E₃).iteratedFDeriv_comp_left
                  (f := lifted) hlifted (i := 2)
                  (by simpa using (show (2 : WithTop ℕ∞) ≤ 3 by norm_num)))
            simpa [lifted, Function.comp, compositionSecondLiftedDirectionDerivative,
              vectorSecondDirectionalDerivative,
              ContinuousLinearMap.compContinuousMultilinearMap_coe] using hfst.symm
          · have hsnd :=
              congrArg
                (fun M : E₁ [×2]→L[ℝ] E₃ => M (fun _ ↦ d))
                ((ContinuousLinearMap.snd ℝ E₂ E₃).iteratedFDeriv_comp_left
                  (f := lifted) hlifted (i := 2)
                  (by simpa using (show (2 : WithTop ℕ∞) ≤ 3 by norm_num)))
            have hsndZero :
                iteratedFDeriv ℝ 2 (Prod.snd ∘ lifted) x (fun _ ↦ d) = 0 := by
              rw [show Prod.snd ∘ lifted = fun _ : E₁ ↦ z by
                funext y
                simp [lifted]]
              simpa using congrArg
                (fun f : E₁ → E₁ [×2]→L[ℝ] E₃ => f x (fun _ ↦ d))
                (iteratedFDeriv_const_of_ne (𝕜 := ℝ) (F := E₃) (n := 2)
                  (by norm_num : (2 : ℕ) ≠ 0) z)
            simpa [lifted, Function.comp, compositionSecondLiftedDirectionDerivative,
              vectorSecondDirectionalDerivative,
              ContinuousLinearMap.compContinuousMultilinearMap_coe] using
              hsnd.symm.trans hsndZero

/-- Helper for Theorem 5.4.6.7: the third iterated derivative of the fixed-`z` lifted line is
`(D³ξ(x)[d, d, d], 0)`. -/
private lemma liftedFixedZLineThirdIteratedDerivEq
    {ξ : E₁ → E₂} {x d : E₁} {z : E₃}
    (hξ : ContDiffAt ℝ 3 ξ x) :
    iteratedDeriv 3 (fun s : ℝ ↦ (ξ (x + s • d), z)) 0 =
      (vectorThirdDirectionalDerivative ξ x d, (0 : E₃)) := by
  let lifted : E₁ → E₂ × E₃ := fun y ↦ (ξ y, z)
  have hlifted : ContDiffAt ℝ 3 lifted x := by
    -- Lift `ξ` to the fixed-`z` pair map before invoking the cubic line-slice chain rule.
    let liftedLp : E₁ → WithLp 2 (E₂ × E₃) := fun y ↦ WithLp.toLp 2 (ξ y, z)
    have hliftedLp : ContDiffAt ℝ 3 liftedLp x := by
      letI : SeminormedAddCommGroup (E₂ × E₃) := Prod.seminormedAddCommGroup
      letI : NormedAddCommGroup (E₂ × E₃) := Prod.normedAddCommGroup
      letI : NormedSpace ℝ (E₂ × E₃) := Prod.normedSpace
      have hpairStd : ContDiffAt ℝ 3 (fun y : E₁ ↦ (ξ y, z)) x := by
        exact hξ.prodMk (contDiffAt_const : ContDiffAt ℝ 3 (fun _ : E₁ ↦ z) x)
      have htoLp :
          ContDiffAt ℝ 3 (fun p : E₂ × E₃ ↦ WithLp.toLp 2 p) (ξ x, z) := by
        simpa [WithLp.prodContinuousLinearEquiv_symm_apply] using
          ((WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃).symm.toContinuousLinearMap.contDiff.contDiffAt :
            ContDiffAt ℝ 3
              ((WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃).symm.toContinuousLinearMap)
              (ξ x, z))
      simpa [liftedLp] using htoLp.comp x hpairStd
    have hofLp :
        ContDiffAt ℝ 3
          (fun w : WithLp 2 (E₂ × E₃) ↦ (WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃) w)
          (liftedLp x) := by
      simpa using
        ((WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃).toContinuousLinearMap.contDiff.contDiffAt :
          ContDiffAt ℝ 3
            ((WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃).toContinuousLinearMap)
            (liftedLp x))
    simpa [lifted, liftedLp] using hofLp.comp x hliftedLp
  calc
    iteratedDeriv 3 (fun s : ℝ ↦ (ξ (x + s • d), z)) 0
      = vectorThirdDirectionalDerivative lifted x d := by
          -- The pair-valued line slice is the standard line slice of the lifted map.
          simpa [lifted] using
            line_slice_iteratedDeriv_three_eq_vectorThirdDirectionalDerivative
              (ξ := lifted) (x := x) (d := d) hlifted
    _ = (vectorThirdDirectionalDerivative ξ x d, (0 : E₃)) := by
          -- Compare the pair-valued third Fréchet derivative through the two coordinate
          -- projections; the constant `z` branch contributes zero.
          ext
          · have hfst :=
              congrArg
                (fun M : E₁ [×3]→L[ℝ] E₂ => M (fun _ ↦ d))
                ((ContinuousLinearMap.fst ℝ E₂ E₃).iteratedFDeriv_comp_left
                  (f := lifted) hlifted (i := 3)
                  (by simpa using (show (3 : WithTop ℕ∞) ≤ 3 by norm_num)))
            simpa [lifted, Function.comp, vectorThirdDirectionalDerivative,
              ContinuousLinearMap.compContinuousMultilinearMap_coe] using hfst.symm
          · have hsnd :=
              congrArg
                (fun M : E₁ [×3]→L[ℝ] E₃ => M (fun _ ↦ d))
                ((ContinuousLinearMap.snd ℝ E₂ E₃).iteratedFDeriv_comp_left
                  (f := lifted) hlifted (i := 3)
                  (by simpa using (show (3 : WithTop ℕ∞) ≤ 3 by norm_num)))
            have hsndZero :
                iteratedFDeriv ℝ 3 (Prod.snd ∘ lifted) x (fun _ ↦ d) = 0 := by
              rw [show Prod.snd ∘ lifted = fun _ : E₁ ↦ z by
                funext y
                simp [lifted]]
              simpa using congrArg
                (fun f : E₁ → E₁ [×3]→L[ℝ] E₃ => f x (fun _ ↦ d))
                (iteratedFDeriv_const_of_ne (𝕜 := ℝ) (F := E₃) (n := 3)
                  (by norm_num : (3 : ℕ) ≠ 0) z)
            simpa [lifted, Function.comp, vectorThirdDirectionalDerivative,
              ContinuousLinearMap.compContinuousMultilinearMap_coe] using
              hsnd.symm.trans hsndZero

/-- Helper for Theorem 5.4.6.7: freezing the `z`-coordinate turns the ambient first derivative of
`Φ` along `(u, 0)` into the `y`-gradient pairing. -/
private lemma horizontalFDerivEqInnerYGradient
    {Φ : E₂ × E₃ → ℝ} {y u : E₂} {z : E₃}
    (hΦ : DifferentiableAt ℝ Φ (y, z)) :
    fderiv ℝ Φ (y, z) (u, (0 : E₃)) =
      inner ℝ (∇ (fun y' : E₂ ↦ Φ (y', z)) y) u := by
  have hslice :
      DifferentiableAt ℝ (fun y' : E₂ ↦ Φ (y', z)) y := by
    -- Freeze `z` by composing `Φ` with the affine embedding `y' ↦ (y', z)`.
    exact (hΦ.hasFDerivAt.comp y (hasFDerivAt_prodMk_left y z)).differentiableAt
  have hleft :
      HasFDerivAt (fun y' : E₂ ↦ Φ (y', z))
        ((fderiv ℝ Φ (y, z)).comp (ContinuousLinearMap.inl ℝ E₂ E₃)) y := by
    -- The derivative of the frozen slice is the ambient derivative composed with the left
    -- product inclusion.
    simpa [Function.comp] using
      hΦ.hasFDerivAt.comp y (hasFDerivAt_prodMk_left y z)
  calc
    fderiv ℝ Φ (y, z) (u, (0 : E₃))
      = fderiv ℝ (fun y' : E₂ ↦ Φ (y', z)) y u := by
          rw [hleft.fderiv]
          simp
    _ = inner ℝ (∇ (fun y' : E₂ ↦ Φ (y', z)) y) u := by
          rw [← inner_gradient_left hslice]

/-- Helper for Theorem 5.4.6.7: the two mixed ambient second-derivative terms collect into
`3 * ⟪∇²Φ(p) u, v⟫`. -/
private lemma mixedSecondTermsEqThreeHessianPairing
    {Φ : E₂ × E₃ → ℝ} {p u v : E₂ × E₃}
    (hΦ : ContDiffAt ℝ 2 Φ p) :
    iteratedFDeriv ℝ 2 Φ p ![v, u] + 2 • iteratedFDeriv ℝ 2 Φ p ![u, v] =
      (3 : ℝ) * inner ℝ (hessian Φ p u) v := by
  -- Use symmetry to orient both mixed second-derivative terms in the same order.
  rw [ambient_iteratedFDeriv_two_swap_at (Φ := Φ) (p := p) (u := v) (v := u) hΦ]
  -- After the orientation rewrite, both terms are the same Hessian pairing.
  rw [ambient_iteratedFDeriv_two_eq_hessian_pairing (Φ := Φ) (p := p) (u := u) (v := v) hΦ]
  ring

/-- Theorem 5.4.6.7: the third directional derivative `Δ₃ = D³ψ(x, z)[d, d, d]` of
`ψ(x, z) = Φ(ξ(x), z)` is the sum of the third derivative of `Φ` in the lifted direction
`l = (Dξ(x)[d], 0)`, three times the mixed Hessian pairing with
`l' = (D²ξ(x)[d, d], 0)`, and the pairing of `∇ᵧ Φ(ξ(x), z)` with `D³ξ(x)[d, d, d]`. -/
theorem compositionPotential_thirdDirectionalDerivative_eq
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x d : E₁} {z : E₃}
    (hξ : ContDiffAt ℝ 3 ξ x)
    (hΦ : ContDiffAt ℝ 3 Φ (ξ x, z)) :
    let l : E₂ × E₃ := (fderiv ℝ ξ x d, 0);
    thirdDirectionalDerivative (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)) x d =
      thirdDirectionalDerivative Φ (ξ x, z) l +
        (3 : ℝ) * inner ℝ (hessian Φ (ξ x, z) l)
          (compositionSecondLiftedDirectionDerivative ξ x d) +
        inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x))
          (vectorThirdDirectionalDerivative ξ x d) := by
  let l : E₂ × E₃ := (fderiv ℝ ξ x d, 0)
  let slice : ℝ → E₂ × E₃ := fun s ↦ (ξ (x + s • d), z)
  have hline₃ : ContDiffAt ℝ 3 (fun s : ℝ ↦ x + s • d) 0 := by
    -- The affine source line is smooth.
    fun_prop
  have hslice_left₃ : ContDiffAt ℝ 3 (fun s : ℝ ↦ ξ (x + s • d)) 0 := by
    -- Compose `ξ` with the affine source line to obtain the one-variable slice in `E₂`.
    simpa [Function.comp] using ContDiffAt.comp (x := 0) (by simpa using hξ) hline₃
  have hslice₃ : ContDiffAt ℝ 3 slice 0 := by
    -- Pair the `E₂`-slice with the constant `z` branch.
    let sliceLp : ℝ → WithLp 2 (E₂ × E₃) := fun s ↦ WithLp.toLp 2 (ξ (x + s • d), z)
    have hsliceLp : ContDiffAt ℝ 3 sliceLp 0 := by
      letI : SeminormedAddCommGroup (E₂ × E₃) := Prod.seminormedAddCommGroup
      letI : NormedAddCommGroup (E₂ × E₃) := Prod.normedAddCommGroup
      letI : NormedSpace ℝ (E₂ × E₃) := Prod.normedSpace
      have hsliceStd : ContDiffAt ℝ 3 (fun s : ℝ ↦ (ξ (x + s • d), z)) 0 := by
        exact hslice_left₃.prodMk (contDiffAt_const : ContDiffAt ℝ 3 (fun _ : ℝ ↦ z) 0)
      have htoLp :
          ContDiffAt ℝ 3 (fun p : E₂ × E₃ ↦ WithLp.toLp 2 p) (ξ x, z) := by
        simpa [WithLp.prodContinuousLinearEquiv_symm_apply] using
          ((WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃).symm.toContinuousLinearMap.contDiff.contDiffAt :
            ContDiffAt ℝ 3
              ((WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃).symm.toContinuousLinearMap)
              (ξ x, z))
      have htoLp0 :
          ContDiffAt ℝ 3
            (fun p : E₂ × E₃ ↦ WithLp.toLp 2 p)
            ((fun s : ℝ ↦ (ξ (x + s • d), z)) 0) := by
        simpa using htoLp
      simpa [sliceLp] using htoLp0.comp 0 hsliceStd
    have hofLp :
        ContDiffAt ℝ 3
          (fun w : WithLp 2 (E₂ × E₃) ↦ (WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃) w)
          (sliceLp 0) := by
      simpa using
        ((WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃).toContinuousLinearMap.contDiff.contDiffAt :
          ContDiffAt ℝ 3
            ((WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃).toContinuousLinearMap)
            (sliceLp 0))
    simpa [slice, sliceLp] using hofLp.comp 0 hsliceLp
  have hsliceDeriv : deriv slice 0 = l := by
    -- The first derivative of the lifted line slice is the lifted direction `l`.
    simpa [l, slice] using liftedFixedZLineDerivEq (ξ := ξ) (x := x) (d := d) (z := z) hξ
  have hsliceSecond :
      iteratedDeriv 2 slice 0 = compositionSecondLiftedDirectionDerivative ξ x d := by
    -- The second derivative of the lifted line slice is the packaged lifted second direction.
    simpa [slice] using
      liftedFixedZLineSecondIteratedDerivEq (ξ := ξ) (x := x) (d := d) (z := z) hξ
  have hsliceThird :
      iteratedDeriv 3 slice 0 = (vectorThirdDirectionalDerivative ξ x d, (0 : E₃)) := by
    -- The third derivative of the lifted line slice is the lifted third directional derivative.
    simpa [slice] using
      liftedFixedZLineThirdIteratedDerivEq (ξ := ξ) (x := x) (d := d) (z := z) hξ
  have hΦslice : ContDiffAt ℝ 3 Φ (slice 0) := by
    simpa [slice] using hΦ
  have hΦ₂ : ContDiffAt ℝ 2 Φ (ξ x, z) := hΦ.of_le (by norm_num)
  have hΦdiff : DifferentiableAt ℝ Φ (ξ x, z) := hΦ.differentiableAt (by norm_num)
  -- Apply the cubic one-variable chain rule to the fixed-`z` lifted slice `Φ ∘ slice`, then
  -- rewrite each derivative input into the source-facing owners from the theorem statement.
  calc
    thirdDirectionalDerivative (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)) x d
      = iteratedDeriv 3 (Φ ∘ slice) 0 := by
          -- Normalize the source-facing directional slice to the one-variable composition
          -- `s ↦ Φ (ξ (x + s • d), z)`.
          rfl
    _ =
        iteratedFDeriv ℝ 3 Φ (slice 0) (fun _ ↦ deriv slice 0) +
          iteratedFDeriv ℝ 2 Φ (slice 0) ![iteratedDeriv 2 slice 0, deriv slice 0] +
          2 • iteratedFDeriv ℝ 2 Φ (slice 0) ![deriv slice 0, iteratedDeriv 2 slice 0] +
          fderiv ℝ Φ (slice 0) (iteratedDeriv 3 slice 0) := by
            exact iteratedDeriv_vcomp_three hΦslice hslice₃
    _ =
        iteratedFDeriv ℝ 3 Φ (ξ x, z) (fun _ ↦ l) +
          iteratedFDeriv ℝ 2 Φ (ξ x, z)
            ![compositionSecondLiftedDirectionDerivative ξ x d, l] +
          2 • iteratedFDeriv ℝ 2 Φ (ξ x, z)
            ![l, compositionSecondLiftedDirectionDerivative ξ x d] +
          fderiv ℝ Φ (ξ x, z) (vectorThirdDirectionalDerivative ξ x d, (0 : E₃)) := by
            -- Substitute the three derivative inputs of the lifted line slice and rewrite
            -- `slice 0` back to `(ξ x, z)`.
            rw [hsliceDeriv, hsliceSecond, hsliceThird]
            simp [slice]
    _ =
        thirdDirectionalDerivative Φ (ξ x, z) l +
          (iteratedFDeriv ℝ 2 Φ (ξ x, z)
              ![compositionSecondLiftedDirectionDerivative ξ x d, l] +
            2 • iteratedFDeriv ℝ 2 Φ (ξ x, z)
              ![l, compositionSecondLiftedDirectionDerivative ξ x d]) +
          fderiv ℝ Φ (ξ x, z) (vectorThirdDirectionalDerivative ξ x d, (0 : E₃)) := by
            -- Rewrite the ambient cubic term as the source-facing third directional derivative.
            rw [thirdDirectionalDerivative_eq_iteratedFDeriv (f := Φ) (x := (ξ x, z)) (u := l) hΦ]
            ring_nf
    _ =
        thirdDirectionalDerivative Φ (ξ x, z) l +
          (3 : ℝ) * inner ℝ (hessian Φ (ξ x, z) l)
            (compositionSecondLiftedDirectionDerivative ξ x d) +
          fderiv ℝ Φ (ξ x, z) (vectorThirdDirectionalDerivative ξ x d, (0 : E₃)) := by
            -- Collect the two mixed ambient second-derivative terms into the single Hessian
            -- pairing with coefficient `3`.
            rw [mixedSecondTermsEqThreeHessianPairing
              (Φ := Φ) (p := (ξ x, z)) (u := l)
              (v := compositionSecondLiftedDirectionDerivative ξ x d) hΦ₂]
    _ =
        thirdDirectionalDerivative Φ (ξ x, z) l +
          (3 : ℝ) * inner ℝ (hessian Φ (ξ x, z) l)
            (compositionSecondLiftedDirectionDerivative ξ x d) +
          inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x))
            (vectorThirdDirectionalDerivative ξ x d) := by
            -- Convert the last ambient first-derivative term to the frozen-`z` `y`-gradient
            -- pairing.
            rw [horizontalFDerivEqInnerYGradient
              (Φ := Φ) (y := ξ x) (u := vectorThirdDirectionalDerivative ξ x d)
              (z := z) hΦdiff]

end
