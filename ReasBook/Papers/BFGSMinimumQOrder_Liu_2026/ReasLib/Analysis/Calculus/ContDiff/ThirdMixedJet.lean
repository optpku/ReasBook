module

public import ReasLib.Analysis.Calculus.ContDiff.CrossDerivative
public import Mathlib.Analysis.Calculus.Deriv.Prod

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.Calculus

/-!
This file provides the parameter-side interface for a third mixed jet.  The
source calculation is allowed to establish vanishing of an evaluated second
jet on a neighbourhood; the adapter differentiates that vanishing identity
without exposing the construction of the underlying second jet.
-/

/-- Helper for Lemma 4.15: a locally zero evaluation of a `C³` second jet has
zero derivative in every parameter direction, hence zero third mixed jet. -/
theorem iteratedFDeriv_three_eq_zero_of_eventually_secondJet_zero
    {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : E → ℝ} {c : Z →L[ℝ] E} {z : Z} (u v : E)
    (hf : ContDiffAt ℝ 3 f (c z))
    (hzero : (fun y : Z ↦ iteratedFDeriv ℝ 2 f (c y) ![u, v]) =ᶠ[𝓝 z]
      (fun _ : Z ↦ (0 : ℝ))) (w : Z) :
    iteratedFDeriv ℝ 3 f (c z) ![c w, u, v] = 0 := by
  let jet : E → (E [×2]→L[ℝ] ℝ) := iteratedFDeriv ℝ 2 f
  let directions : Fin 2 → E := ![u, v]
  let evaluated : E → ℝ := fun x ↦ jet x (directions)
  let parameterized : Z → ℝ := fun y ↦ evaluated (c y)
  have horder : (1 : WithTop ℕ∞) + 2 ≤ (3 : WithTop ℕ∞) := by
    norm_num
  have hone : (1 : WithTop ℕ∞) ≠ 0 := by
    norm_num
  have hjet : ContDiffAt ℝ 1 jet (c z) := by
    exact hf.iteratedFDeriv_right horder
  have hevaluated : ContDiffAt ℝ 1 evaluated (c z) := by
    let evaluator : (E [×2]→L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ E) ℝ directions
    have hevaluator : ContDiffAt ℝ 1 evaluator (jet (c z)) :=
      evaluator.contDiff.contDiffAt
    have hcomposed := hevaluator.comp (c z) hjet
    simpa only [evaluated, evaluator, Function.comp_def,
      ContinuousMultilinearMap.apply_apply] using hcomposed
  have hparameterized : ContDiffAt ℝ 1 parameterized z := by
    exact hevaluated.comp z c.contDiff.contDiffAt
  have hzero' : parameterized =ᶠ[𝓝 z] (fun _ : Z ↦ (0 : ℝ)) := by
    simpa only [parameterized, evaluated, jet, directions] using hzero
  have hparameterized_zero : HasFDerivAt parameterized (0 : Z →L[ℝ] ℝ) z := by
    exact (hasFDerivAt_const (x := z) (c := (0 : ℝ))).congr_of_eventuallyEq hzero'
  have hparameterized_fderiv : fderiv ℝ parameterized z = 0 := by
    exact hparameterized_zero.fderiv
  have hevaluated_fderiv :
      fderiv ℝ evaluated (c z) (c w) =
        (fderiv ℝ jet (c z)) (c w) directions := by
    exact fderiv_continuousMultilinear_apply_const_apply
      (hjet.differentiableAt hone) directions (c w)
  have hparameterized_fderiv_apply :
      fderiv ℝ parameterized z w = fderiv ℝ evaluated (c z) (c w) := by
    have hevalDiff : DifferentiableAt ℝ evaluated (c z) :=
      hevaluated.differentiableAt hone
    have hcomp := hevalDiff.hasFDerivAt.comp z c.hasFDerivAt
    have hcompApply := congrArg (fun L : Z →L[ℝ] ℝ ↦ L w) hcomp.fderiv
    simpa only [parameterized, Function.comp_def, ContinuousLinearMap.comp_apply] using hcompApply
  have hthird :
      (fderiv ℝ jet (c z)) (c w) directions = 0 := by
    rw [← hevaluated_fderiv, ← hparameterized_fderiv_apply]
    exact congrArg (fun L : Z →L[ℝ] ℝ ↦ L w) hparameterized_fderiv
  have hthird' :
      iteratedFDeriv ℝ 3 f (c z) ![c w, u, v] =
        (fderiv ℝ jet (c z)) (c w) directions := by
    rw [iteratedFDeriv_succ_apply_left]
    rfl
  rw [hthird']
  exact hthird

/-- Helper for Lemma 4.15: the same vanishing conclusion holds after translating
   the parameter slice by a fixed base point. -/
theorem iteratedFDeriv_three_eq_zero_of_eventually_affine_secondJet_zero
    {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : E → ℝ} {a : E} {c : Z →L[ℝ] E} {z : Z} (u v : E)
    (hf : ContDiffAt ℝ 3 f (a + c z))
    (hzero :
      (fun y : Z ↦ iteratedFDeriv ℝ 2 f (a + c y) ![u, v]) =ᶠ[𝓝 z]
        (fun _ : Z ↦ (0 : ℝ))) (w : Z) :
    iteratedFDeriv ℝ 3 f (a + c z) ![c w, u, v] = 0 := by
  let jet : E → (E [×2]→L[ℝ] ℝ) := iteratedFDeriv ℝ 2 f
  let directions : Fin 2 → E := ![u, v]
  let evaluated : E → ℝ := fun x ↦ jet x directions
  let affine : Z → E := fun y ↦ a + c y
  let parameterized : Z → ℝ := fun y ↦ evaluated (affine y)
  have horder : (1 : WithTop ℕ∞) + 2 ≤ (3 : WithTop ℕ∞) := by
    norm_num
  have hone : (1 : WithTop ℕ∞) ≠ 0 := by
    norm_num
  have hjet : ContDiffAt ℝ 1 jet (affine z) := by
    simpa only [affine] using hf.iteratedFDeriv_right horder
  have hevaluated : ContDiffAt ℝ 1 evaluated (affine z) := by
    let evaluator : (E [×2]→L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ E) ℝ directions
    have hevaluator : ContDiffAt ℝ 1 evaluator (jet (affine z)) :=
      evaluator.contDiff.contDiffAt
    have hcomposed := hevaluator.comp (affine z) hjet
    simpa only [evaluated, evaluator, Function.comp_def,
      ContinuousMultilinearMap.apply_apply] using hcomposed
  have haffine : HasFDerivAt affine c z := by
    have hconstant : HasFDerivAt (fun _ : Z ↦ a) (0 : Z →L[ℝ] E) z :=
      hasFDerivAt_const (𝕜 := ℝ) (x := z) (c := a)
    have hlinear : HasFDerivAt (fun y : Z ↦ c y) c z := c.hasFDerivAt
    have hsum := hconstant.add hlinear
    have hfun : (fun x : Z ↦ a) + (fun y : Z ↦ c y) = affine := by
      funext y
      rfl
    rw [hfun] at hsum
    simpa only [zero_add] using hsum
  have haffineCont : ContDiffAt ℝ 1 affine z := by
    fun_prop
  have hparameterized : ContDiffAt ℝ 1 parameterized z := by
    exact hevaluated.comp z haffineCont
  have hzero' : parameterized =ᶠ[𝓝 z] (fun _ : Z ↦ (0 : ℝ)) := by
    simpa only [parameterized, evaluated, affine, jet, directions] using hzero
  have hparameterized_zero : HasFDerivAt parameterized (0 : Z →L[ℝ] ℝ) z := by
    exact (hasFDerivAt_const (x := z) (c := (0 : ℝ))).congr_of_eventuallyEq hzero'
  have hparameterized_fderiv : fderiv ℝ parameterized z = 0 := by
    exact hparameterized_zero.fderiv
  have hevaluated_fderiv :
      fderiv ℝ evaluated (affine z) (c w) =
        (fderiv ℝ jet (affine z)) (c w) directions := by
    exact fderiv_continuousMultilinear_apply_const_apply
      (hjet.differentiableAt hone) directions (c w)
  have hparameterized_fderiv_apply :
      fderiv ℝ parameterized z w = fderiv ℝ evaluated (affine z) (c w) := by
    have hevalDiff : DifferentiableAt ℝ evaluated (affine z) :=
      hevaluated.differentiableAt hone
    have hcomp := hevalDiff.hasFDerivAt.comp z haffine
    have hcompApply := congrArg (fun L : Z →L[ℝ] ℝ ↦ L w) hcomp.fderiv
    simpa only [parameterized, Function.comp_def, ContinuousLinearMap.comp_apply] using hcompApply
  have hthird :
      (fderiv ℝ jet (affine z)) (c w) directions = 0 := by
    rw [← hevaluated_fderiv, ← hparameterized_fderiv_apply]
    exact congrArg (fun L : Z →L[ℝ] ℝ ↦ L w) hparameterized_fderiv
  have hthird' :
      iteratedFDeriv ℝ 3 f (affine z) ![c w, u, v] =
        (fderiv ℝ jet (affine z)) (c w) directions := by
    rw [iteratedFDeriv_succ_apply_left]
    rfl
  rw [hthird']
  exact hthird

/-- Helper for Lemma 4.15: a locally zero affine second jet has zero third mixed jet for an
arbitrary normed target, so vector-valued observables use the same parameter-side interface. -/
theorem iteratedFDeriv_three_eq_zero_of_eventually_affine_secondJet_zero_target
    {E F Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : E → F} {a : E} {c : Z →L[ℝ] E} {z : Z}
    (u v : E)
    (hf : ContDiffAt ℝ 3 f (a + c z))
    (hzero :
      (fun y : Z ↦ iteratedFDeriv ℝ 2 f (a + c y) ![u, v]) =ᶠ[𝓝 z]
        (fun _ : Z ↦ (0 : F))) (w : Z) :
    iteratedFDeriv ℝ 3 f (a + c z) ![c w, u, v] = 0 := by
  let jet : E → (E [×2]→L[ℝ] F) := iteratedFDeriv ℝ 2 f
  let directions : Fin 2 → E := ![u, v]
  let evaluated : E → F := fun x ↦ jet x directions
  let affine : Z → E := fun y ↦ a + c y
  let parameterized : Z → F := fun y ↦ evaluated (affine y)
  have horder : (1 : WithTop ℕ∞) + 2 ≤ (3 : WithTop ℕ∞) := by
    norm_num
  have hone : (1 : WithTop ℕ∞) ≠ 0 := by
    norm_num
  have hjet : ContDiffAt ℝ 1 jet (affine z) := by
    simpa only [affine] using hf.iteratedFDeriv_right horder
  have hevaluated : ContDiffAt ℝ 1 evaluated (affine z) := by
    let evaluator : (E [×2]→L[ℝ] F) →L[ℝ] F :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ E) F directions
    have hevaluator : ContDiffAt ℝ 1 evaluator (jet (affine z)) :=
      evaluator.contDiff.contDiffAt
    have hcomposed := hevaluator.comp (affine z) hjet
    simpa only [evaluated, evaluator, Function.comp_def,
      ContinuousMultilinearMap.apply_apply] using hcomposed
  have haffine : HasFDerivAt affine c z := by
    have hconstant : HasFDerivAt (fun _ : Z ↦ a) (0 : Z →L[ℝ] E) z :=
      hasFDerivAt_const (𝕜 := ℝ) (x := z) (c := a)
    have hlinear : HasFDerivAt (fun y : Z ↦ c y) c z := c.hasFDerivAt
    have hsum := hconstant.add hlinear
    have hfun : (fun x : Z ↦ a) + (fun y : Z ↦ c y) = affine := by
      funext y
      rfl
    rw [hfun] at hsum
    simpa only [zero_add] using hsum
  have haffineCont : ContDiffAt ℝ 1 affine z := by
    fun_prop
  have hparameterized : ContDiffAt ℝ 1 parameterized z := by
    exact hevaluated.comp z haffineCont
  have hzero' : parameterized =ᶠ[𝓝 z] (fun _ : Z ↦ (0 : F)) := by
    simpa only [parameterized, evaluated, affine, jet, directions] using hzero
  have hparameterized_zero : HasFDerivAt parameterized (0 : Z →L[ℝ] F) z := by
    exact (hasFDerivAt_const (x := z) (c := (0 : F))).congr_of_eventuallyEq hzero'
  have hparameterized_fderiv : fderiv ℝ parameterized z = 0 := by
    exact hparameterized_zero.fderiv
  have hevaluated_fderiv :
      fderiv ℝ evaluated (affine z) (c w) =
        (fderiv ℝ jet (affine z)) (c w) directions := by
    exact fderiv_continuousMultilinear_apply_const_apply
      (hjet.differentiableAt hone) directions (c w)
  have hparameterized_fderiv_apply :
      fderiv ℝ parameterized z w = fderiv ℝ evaluated (affine z) (c w) := by
    have hevalDiff : DifferentiableAt ℝ evaluated (affine z) :=
      hevaluated.differentiableAt hone
    have hcomp := hevalDiff.hasFDerivAt.comp z haffine
    have hcompApply := congrArg (fun L : Z →L[ℝ] F ↦ L w) hcomp.fderiv
    simpa only [parameterized, Function.comp_def, ContinuousLinearMap.comp_apply] using hcompApply
  have hthird :
      (fderiv ℝ jet (affine z)) (c w) directions = 0 := by
    rw [← hevaluated_fderiv, ← hparameterized_fderiv_apply]
    exact congrArg (fun L : Z →L[ℝ] F ↦ L w) hparameterized_fderiv
  have hthird' :
      iteratedFDeriv ℝ 3 f (affine z) ![c w, u, v] =
        (fderiv ℝ jet (affine z)) (c w) directions := by
    rw [iteratedFDeriv_succ_apply_left]
    rfl
  rw [hthird']
  exact hthird

/-- Helper for Lemma 4.15: the affine bridge extends to any `C¹` parameter path whose derivative
is the prescribed linear map, which isolates nonlinear reparameterizations from the jet proof. -/
theorem iteratedFDeriv_three_eq_zero_of_eventually_secondJet_zero_along_path
    {E F Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : E → F} {φ : Z → E} {c : Z →L[ℝ] E} {z : Z}
    (u v : E)
    (hf : ContDiffAt ℝ 3 f (φ z))
    (hφ : ContDiffAt ℝ 1 φ z)
    (hφderiv : HasFDerivAt φ c z)
    (hzero :
      (fun y : Z ↦ iteratedFDeriv ℝ 2 f (φ y) ![u, v]) =ᶠ[𝓝 z]
        (fun _ : Z ↦ (0 : F))) (w : Z) :
    iteratedFDeriv ℝ 3 f (φ z) ![c w, u, v] = 0 := by
  let jet : E → (E [×2]→L[ℝ] F) := iteratedFDeriv ℝ 2 f
  let directions : Fin 2 → E := ![u, v]
  let evaluated : E → F := fun x ↦ jet x directions
  let parameterized : Z → F := fun y ↦ evaluated (φ y)
  have horder : (1 : WithTop ℕ∞) + 2 ≤ (3 : WithTop ℕ∞) := by
    norm_num
  have hone : (1 : WithTop ℕ∞) ≠ 0 := by
    norm_num
  have hjet : ContDiffAt ℝ 1 jet (φ z) := by
    exact hf.iteratedFDeriv_right horder
  have hevaluated : ContDiffAt ℝ 1 evaluated (φ z) := by
    let evaluator : (E [×2]→L[ℝ] F) →L[ℝ] F :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ E) F directions
    have hevaluator : ContDiffAt ℝ 1 evaluator (jet (φ z)) :=
      evaluator.contDiff.contDiffAt
    have hcomposed := hevaluator.comp (φ z) hjet
    simpa only [evaluated, evaluator, Function.comp_def,
      ContinuousMultilinearMap.apply_apply] using hcomposed
  have hparameterized : ContDiffAt ℝ 1 parameterized z := by
    exact hevaluated.comp z hφ
  have hzero' : parameterized =ᶠ[𝓝 z] (fun _ : Z ↦ (0 : F)) := by
    simpa only [parameterized, evaluated, jet, directions] using hzero
  have hparameterized_zero : HasFDerivAt parameterized (0 : Z →L[ℝ] F) z := by
    exact (hasFDerivAt_const (x := z) (c := (0 : F))).congr_of_eventuallyEq hzero'
  have hparameterized_fderiv : fderiv ℝ parameterized z = 0 := by
    exact hparameterized_zero.fderiv
  have hevaluated_fderiv :
      fderiv ℝ evaluated (φ z) (c w) =
        (fderiv ℝ jet (φ z)) (c w) directions := by
    exact fderiv_continuousMultilinear_apply_const_apply
      (hjet.differentiableAt hone) directions (c w)
  have hparameterized_fderiv_apply :
      fderiv ℝ parameterized z w = fderiv ℝ evaluated (φ z) (c w) := by
    have hevalDiff : DifferentiableAt ℝ evaluated (φ z) :=
      hevaluated.differentiableAt hone
    have hcomp := hevalDiff.hasFDerivAt.comp z hφderiv
    have hcompApply := congrArg (fun L : Z →L[ℝ] F ↦ L w) hcomp.fderiv
    simpa only [parameterized, Function.comp_def, ContinuousLinearMap.comp_apply] using hcompApply
  have hthird :
      (fderiv ℝ jet (φ z)) (c w) directions = 0 := by
    rw [← hevaluated_fderiv, ← hparameterized_fderiv_apply]
    exact congrArg (fun L : Z →L[ℝ] F ↦ L w) hparameterized_fderiv
  have hthird' :
      iteratedFDeriv ℝ 3 f (φ z) ![c w, u, v] =
        (fderiv ℝ jet (φ z)) (c w) directions := by
    rw [iteratedFDeriv_succ_apply_left]
    rfl
  rw [hthird']
  exact hthird

/--
Helper for Infrastructure I.16a: vanishing of every fixed-direction second jet
   along a parameter path gives the corresponding vanishing third mixed jet for all
   parameter and fibre directions.
-/
theorem iteratedFDeriv_three_eq_zero_of_eventually_secondJet_zero_all_directions
    {E F Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : E → F} {φ : Z → E} {c : Z →L[ℝ] E} {z : Z}
    (hf : ContDiffAt ℝ 3 f (φ z))
    (hφ : ContDiffAt ℝ 1 φ z)
    (hφderiv : HasFDerivAt φ c z)
    (hzero : ∀ u v : E,
      (fun y : Z ↦ iteratedFDeriv ℝ 2 f (φ y) ![u, v]) =ᶠ[𝓝 z]
        (fun _ : Z ↦ (0 : F))) :
    ∀ (w : Z) (u v : E),
      iteratedFDeriv ℝ 3 f (φ z) ![c w, u, v] = 0 := by
  intro w u v
  exact iteratedFDeriv_three_eq_zero_of_eventually_secondJet_zero_along_path
    u v hf hφ hφderiv (hzero u v) w

/--
Helper for Infrastructure I.16a: if the parameter derivative is onto, the
   preceding pathwise statement removes the restriction on the first third-jet
   direction.
-/
theorem iteratedFDeriv_three_eq_zero_of_eventually_secondJet_zero_surjective
    {E F Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : E → F} {φ : Z → E} {c : Z →L[ℝ] E} {z : Z}
    (hf : ContDiffAt ℝ 3 f (φ z))
    (hφ : ContDiffAt ℝ 1 φ z)
    (hφderiv : HasFDerivAt φ c z)
    (hc : Function.Surjective c)
    (hzero : ∀ u v : E,
      (fun y : Z ↦ iteratedFDeriv ℝ 2 f (φ y) ![u, v]) =ᶠ[𝓝 z]
        (fun _ : Z ↦ (0 : F)))
    (a b d : E) :
    iteratedFDeriv ℝ 3 f (φ z) ![a, b, d] = 0 := by
  obtain ⟨w, hw⟩ := hc a
  have hvanish := iteratedFDeriv_three_eq_zero_of_eventually_secondJet_zero_along_path
    b d hf hφ hφderiv (hzero b d) w
  rw [← hw]
  exact hvanish

/-- Helper for Infrastructure I.16a: under a surjective parameter derivative, the
   entire third iterated derivative vanishes when its second-jet slices vanish
   locally along the parameter path.
-/
theorem iteratedFDeriv_three_eq_zero_of_eventually_secondJet_zero_surjective_map
    {E F Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : E → F} {φ : Z → E} {c : Z →L[ℝ] E} {z : Z}
    (hf : ContDiffAt ℝ 3 f (φ z))
    (hφ : ContDiffAt ℝ 1 φ z)
    (hφderiv : HasFDerivAt φ c z)
    (hc : Function.Surjective c)
    (hzero : ∀ u v : E,
      (fun y : Z ↦ iteratedFDeriv ℝ 2 f (φ y) ![u, v]) =ᶠ[𝓝 z]
        (fun _ : Z ↦ (0 : F))) :
    iteratedFDeriv ℝ 3 f (φ z) = 0 := by
  apply ContinuousMultilinearMap.ext
  intro directions
  obtain ⟨w, hw⟩ := hc (directions 0)
  have hvanish := iteratedFDeriv_three_eq_zero_of_eventually_secondJet_zero_along_path
    (directions 1) (directions 2) hf hφ hφderiv
      (hzero (directions 1) (directions 2)) w
  have hdirections : directions = ![directions 0, directions 1, directions 2] := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
  rw [hdirections]
  rw [← hw]
  exact hvanish

/-- Helper for Infrastructure I.16a and Lemma 4.15: the second iterated
derivative of a scalar affine scale slice agrees with the full Fréchet second
derivative on the corresponding scale directions. -/
theorem iteratedFDeriv_two_affineScaleSlice_eq_full
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (f : ℝ × Z → ℝ) (z : Z)
    (hf : ContDiffAt ℝ 3 f ((0 : ℝ), z)) :
    iteratedFDeriv ℝ 2 (fun ε : ℝ ↦ f (ε, z)) 0 ![(1 : ℝ), (1 : ℝ)] =
      iteratedFDeriv ℝ 2 f ((0 : ℝ), z)
        ![((1 : ℝ), (0 : Z)), ((1 : ℝ), (0 : Z))] := by
  let s : ℝ → ℝ := fun ε ↦ f (ε, z)
  let x : ℝ × Z := ((0 : ℝ), z)
  let scale : ℝ × Z := ((1 : ℝ), (0 : Z))
  let path : ℝ → ℝ × Z := fun ε ↦ (ε, z)
  have hone : (1 : WithTop ℕ∞) ≠ 0 := by
    norm_num
  have htwo : (2 : WithTop ℕ∞) ≠ 0 := by
    norm_num
  have hthree : (3 : WithTop ℕ∞) ≠ 0 := by
    norm_num
  have hthreeFinite : (3 : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    norm_num
  have hpath : HasDerivAt path scale 0 := by
    have hfirst : HasDerivAt (fun ε : ℝ ↦ ε) 1 0 :=
      hasDerivAt_id (0 : ℝ)
    have hsecond : HasDerivAt (fun _ : ℝ ↦ z) 0 0 :=
      hasDerivAt_const (0 : ℝ) z
    have hprod := HasDerivAt.prodMk hfirst hsecond
    simpa only [path, scale] using hprod
  have horder : (2 : WithTop ℕ∞) + 1 ≤ (3 : WithTop ℕ∞) := by
    norm_num
  have hderivContDiff : ContDiffAt ℝ 2 (fderiv ℝ f) x := by
    exact hf.fderiv_right horder
  have hderivAlongPath : HasDerivAt (fderiv ℝ f ∘ path)
      ((fderiv ℝ (fderiv ℝ f) x) scale) 0 := by
    exact (hderivContDiff.differentiableAt htwo).hasFDerivAt.comp_hasDerivAt 0 hpath
  have hscaleConstant : HasDerivAt (fun _ : ℝ ↦ scale) 0 0 :=
    hasDerivAt_const (0 : ℝ) scale
  have hscaleDerivative := hderivAlongPath.clm_apply hscaleConstant
  have hscaleDerivative' : HasDerivAt
      (fun ε : ℝ ↦ (fderiv ℝ f (path ε)) scale)
      (((fderiv ℝ (fderiv ℝ f) x) scale) scale) 0 := by
    apply hscaleDerivative.congr_deriv
    simp only [ContinuousLinearMap.map_zero, add_zero]
  have hsCont : ContDiffAt ℝ 3 s 0 := by
    have hpathCont : ContDiffAt ℝ 3 path 0 := by
      fun_prop
    have hcomp := hf.comp 0 hpathCont
    simpa only [s, path, Function.comp_def] using hcomp
  have hsDiff : DifferentiableAt ℝ (fderiv ℝ s) 0 := by
    have horder' : (1 : WithTop ℕ∞) + 1 ≤ (3 : WithTop ℕ∞) := by
      norm_num
    exact (hsCont.fderiv_right horder').differentiableAt hone
  have hclm := fderiv_clm_apply hsDiff
    (differentiableAt_const (x := (0 : ℝ)) (c := (1 : ℝ)))
  have hclm_apply := congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) hclm
  have hinnerEq :
      (fun ε : ℝ ↦ (fderiv ℝ s ε) 1) = (fun ε : ℝ ↦ deriv s ε) := by
    funext ε
    rw [fderiv_apply_one_eq_deriv]
  rw [hinnerEq] at hclm_apply
  have hconstFDeriv : fderiv ℝ (fun _ : ℝ ↦ (1 : ℝ)) 0 = 0 := by
    exact (hasFDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).fderiv
  rw [hconstFDeriv] at hclm_apply
  have hsecond_slice :
      deriv (fun ε : ℝ ↦ deriv s ε) 0 =
        (fderiv ℝ (fderiv ℝ s) 0) 1 1 := by
    have hrew := hclm_apply
    rw [fderiv_apply_one_eq_deriv] at hrew
    simpa only [ContinuousLinearMap.comp_zero, zero_apply, add_zero,
      zero_add, ContinuousLinearMap.flip_apply] using hrew
  have hsliceEq :
      (fun ε : ℝ ↦ deriv s ε) =ᶠ[𝓝 (0 : ℝ)]
        (fun ε : ℝ ↦ (fderiv ℝ f (path ε)) scale) := by
    have hdiffEventually : ∀ᶠ y : ℝ × Z in 𝓝 x,
        DifferentiableAt ℝ f y := by
      filter_upwards [hf.eventually hthreeFinite] with y hy
      exact hy.differentiableAt hthree
    have hpathTendsto : Tendsto path (𝓝 (0 : ℝ)) (𝓝 x) := by
      have hzero : path 0 = x := by
        simp only [path, x]
      rw [← hzero]
      exact hpath.continuousAt
    have hdiffPath : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
        DifferentiableAt ℝ f (path ε) :=
      hpathTendsto.eventually hdiffEventually
    filter_upwards [hdiffPath] with ε hε
    have hinner : HasDerivAt (fun t : ℝ ↦ (t, z)) scale ε := by
      have hfirst : HasDerivAt (fun t : ℝ ↦ t) 1 ε :=
        hasDerivAt_id ε
      have hsecond : HasDerivAt (fun _ : ℝ ↦ z) 0 ε :=
        hasDerivAt_const ε z
      have hprod := HasDerivAt.prodMk hfirst hsecond
      simpa only [scale] using hprod
    have hchain := hε.hasFDerivAt.comp_hasDerivAt ε hinner
    have hchain' : HasDerivAt (fun t : ℝ ↦ f (t, z))
        ((fderiv ℝ f (path ε)) scale) ε := by
      simpa only [path, Function.comp_def] using hchain
    exact hchain'.deriv
  have hsliceDeriv : HasDerivAt
      (fun ε : ℝ ↦ deriv s ε)
      (((fderiv ℝ (fderiv ℝ f) x) scale) scale) 0 := by
    exact hscaleDerivative'.congr_of_eventuallyEq hsliceEq
  have hsliceDerivValue := hsliceDeriv.deriv
  have hiterSlice :
      iteratedFDeriv ℝ 2 (fun ε : ℝ ↦ f (ε, z)) 0 ![(1 : ℝ), (1 : ℝ)] =
        deriv (fun ε : ℝ ↦ deriv (fun t : ℝ ↦ f (t, z)) ε) 0 := by
    rw [iteratedFDeriv_two_apply]
    simpa only [s, Matrix.cons_val_zero, Matrix.cons_val_one] using hsecond_slice.symm
  calc
    iteratedFDeriv ℝ 2 (fun ε : ℝ ↦ f (ε, z)) 0 ![(1 : ℝ), (1 : ℝ)] =
        deriv (fun ε : ℝ ↦ deriv (fun t : ℝ ↦ f (t, z)) ε) 0 := hiterSlice
    _ = (((fderiv ℝ (fderiv ℝ f) x) scale) scale) := hsliceDerivValue
    _ = iteratedFDeriv ℝ 2 f x ![scale, scale] := by
      rw [iteratedFDeriv_two_apply]
      rfl

end DFP.Calculus
