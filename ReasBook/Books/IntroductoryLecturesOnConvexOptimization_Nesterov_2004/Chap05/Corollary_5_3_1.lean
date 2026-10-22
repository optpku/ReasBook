/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Analysis.InnerProductSpace.ProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Set Topology
open scoped Gradient HessianLocalNorm

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Helper for Corollary 5.3.1: the strict epigraph `{(x, t) | x ∈ dom ∧ f x < t}` on raw
pairs. -/
def strictConstrainedEpigraph (dom : Set E) (f : E → ℝ) : Set (E × ℝ) :=
  {p | p.1 ∈ dom ∧ f p.1 < p.2}

/-- Helper for Corollary 5.3.1: membership in `strictConstrainedEpigraph dom f` is the textbook
strict epigraph condition. -/
@[simp] theorem mem_strictConstrainedEpigraph_iff
    {dom : Set E} {f : E → ℝ} {p : E × ℝ} :
    p ∈ strictConstrainedEpigraph dom f ↔ p.1 ∈ dom ∧ f p.1 < p.2 :=
  Iff.rfl

/-- Helper for Corollary 5.3.1: the textbook epigraph barrier
`(x, t) ↦ f x - log (t - f x)` on raw pairs. -/
def epigraphLogBarrier (f : E → ℝ) : E × ℝ → ℝ :=
  fun p ↦ f p.1 + sublevelLogBarrier (fun q : E × ℝ ↦ f q.1 - q.2) 0 p

/-- Helper for Corollary 5.3.1: evaluating `epigraphLogBarrier f` recovers the textbook
raw-pair formula. -/
@[simp] theorem epigraphLogBarrier_apply (f : E → ℝ) (p : E × ℝ) :
    epigraphLogBarrier f p = f p.1 - Real.log (p.2 - f p.1) := by
  simp [epigraphLogBarrier, sublevelLogBarrier, sub_eq_add_neg, add_comm]

noncomputable local instance instLocalChap05_Corollary_5_3_11 : SeminormedAddCommGroup (E × ℝ) :=
  WithLp.seminormedAddCommGroupToProd 2 E ℝ

noncomputable local instance instLocalChap05_Corollary_5_3_12 : NormedAddCommGroup (E × ℝ) :=
  WithLp.normedAddCommGroupToProd 2 E ℝ

noncomputable local instance instLocalChap05_Corollary_5_3_13 : NormedSpace ℝ (E × ℝ) :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 E ℝ

noncomputable local instance instInnerProductSpaceChap05_Corollary_5_3_11 : InnerProductSpace ℝ (E × ℝ) where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 E ℝ x]
    exact InnerProductSpace.norm_sq_eq_re_inner (WithLp.toLp 2 x)
  conj_inner_symm x y := by
    change inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 x) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_comm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  add_left x y z := by
    change inner ℝ (WithLp.toLp 2 x + WithLp.toLp 2 y) (WithLp.toLp 2 z) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 z) +
        inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 z)
    simpa using
      (inner_add_left
        (𝕜 := ℝ)
        (E := WithLp 2 (E × ℝ))
        (WithLp.toLp 2 x)
        (WithLp.toLp 2 y)
        (WithLp.toLp 2 z))
  smul_left x y r := by
    change inner ℝ (r • WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      r * inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_smul_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) r

noncomputable local instance instLocalChap05_Corollary_5_3_14 : CompleteSpace (E × ℝ) := inferInstance

local notation "Z" => WithLp 2 (E × ℝ)
local notation "ofZ" => (WithLp.ofLp : Z → E × ℝ)

/-- Helper for Corollary 5.3.1: on `ℝ`, the real inner product is ordinary multiplication. -/
@[simp] private theorem real_inner_eq_mul (s t : ℝ) :
    inner ℝ s t = s * t := by
  -- Rewrite the inner product through scalar multiplication by `1`.
  calc
    inner ℝ s t = inner ℝ (s • (1 : ℝ)) t := by simp
    _ = s * inner ℝ (1 : ℝ) t := by rw [real_inner_smul_left]
    _ = s * t := by
          congr 1
          calc
            inner ℝ (1 : ℝ) t = inner ℝ (1 : ℝ) (t • (1 : ℝ)) := by simp
            _ = t * inner ℝ (1 : ℝ) (1 : ℝ) := by rw [inner_smul_right]
            _ = t := by simp

/-- Helper for Corollary 5.3.1: the raw `L²` inner product on pairs splits into the first
coordinate inner product and the scalar product of the second coordinates. -/
@[simp] private theorem inner_pair_eq
    (x y : E) (s t : ℝ) :
    inner ℝ (x, s) (y, t) = inner ℝ x y + s * t := by
  -- Expand the pair inner product through the canonical `WithLp` owner.
  change inner ℝ (WithLp.toLp 2 (x, s)) (WithLp.toLp 2 (y, t)) = inner ℝ x y + s * t
  simp [real_inner_eq_mul]

/-- Helper for Corollary 5.3.1: the linear perturbation used in the raw gap theorem is exactly
the negated second coordinate. -/
@[simp] private theorem raw_gap_linear_term_normalization
    (p : E × ℝ) :
    inner ℝ ((0 : E), (-1 : ℝ)) p = -p.2 := by
  -- Expand the pair inner product and simplify the scalar coordinate.
  simpa using inner_pair_eq (x := (0 : E)) (y := p.1) (s := (-1 : ℝ)) (t := p.2)

/-- Helper for Corollary 5.3.1: a `C²` real-valued map has differentiable gradient at the same
point. This is the standard Fréchet-calculus bridge used to rewrite second directional
derivatives as Hessian quadratic forms. -/
private theorem differentiableAt_gradient_of_contDiffAt_two
    {E₁ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
    {g : E₁ → ℝ} {x : E₁} (hg : ContDiffAt ℝ 2 g x) :
    DifferentiableAt ℝ (∇ g) x := by
  let D : StrongDual ℝ E₁ →L[ℝ] E₁ :=
    (InnerProductSpace.toDual ℝ E₁).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ g) x := by
    exact
      (hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  -- The gradient is the inverse Riesz map applied to the Fréchet derivative.
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ g y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Corollary 5.3.1: the raw epigraph gap `(x, t) ↦ f x - t` is standard
self-concordant on the strip `x ∈ dom`. -/
private theorem raw_gap_isStandardSelfConcordantOn
    {dom : Set E} {f : E → ℝ}
    (h : IsStandardSelfConcordantOn dom f) :
    IsStandardSelfConcordantOn
      {p : E × ℝ | p.1 ∈ dom}
      (fun p : E × ℝ ↦ f p.1 - p.2) := by
  let strip : Set (E × ℝ) := {p : E × ℝ | p.1 ∈ dom}
  let fstAffine : E × ℝ →ᴬ[ℝ] E := (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap
  let Fbase : E × ℝ → ℝ := fun p ↦ f p.1
  let Flin : E × ℝ → ℝ := fun p ↦ -p.2
  let gap : E × ℝ → ℝ := Fbase + Flin
  have hpull :
      IsStandardSelfConcordantOn
        strip
        Fbase := by
    -- Pull the base owner back to the raw-pair strip via the first projection.
    simpa [strip, Fbase, fstAffine, Function.comp] using h.comp_continuousAffineMap fstAffine
  have hlin_contDiffOn : ContDiffOn ℝ 3 Flin strip := by
    intro p hp
    simpa [Flin] using (((ContinuousLinearMap.snd ℝ E ℝ).contDiff.contDiffAt).neg.contDiffWithinAt)
  have hlin_convexOn : ConvexOn ℝ strip Flin := by
    refine ⟨hpull.convexOn.1, ?_⟩
    intro x hx y hy a b ha hb hab
    rcases x with ⟨x₁, x₂⟩
    rcases y with ⟨y₁, y₂⟩
    simp [Flin, mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
  have hgap_contDiffOn : ContDiffOn ℝ 3 gap strip := hpull.contDiffOn.add hlin_contDiffOn
  have hgap_convexOn : ConvexOn ℝ strip gap := hpull.convexOn.add hlin_convexOn
  have hgap_std : IsStandardSelfConcordantOn strip gap := by
    refine
    { isOpen_domain := hpull.isOpen_domain
      contDiffOn := hgap_contDiffOn
      convexOn := hgap_convexOn
      third_deriv_bound := by
        intro p hp u
        rcases p with ⟨x, t⟩
        rcases u with ⟨hdir, τ⟩
        let aff : ℝ → ℝ := fun a : ℝ ↦ -t - a * τ
        have hpairLine3 : ContDiffAt ℝ 3 (fun a : ℝ ↦ (x, t) + a • (hdir, τ)) 0 := by
          simpa using
            (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const) :
              ContDiffAt ℝ 3 (fun a : ℝ ↦ (x, t) + a • (hdir, τ)) 0)
        have hbase_at : ContDiffAt ℝ 3 Fbase (x, t) := by
          exact hpull.contDiffOn.contDiffAt (hpull.isOpen_domain.mem_nhds hp)
        have hbase_at_line :
            ContDiffAt ℝ 3 Fbase ((fun a : ℝ ↦ (x, t) + a • (hdir, τ)) 0) := by
          simpa using hbase_at
        have hbase_slice3 : ContDiffAt ℝ 3 (directionalSlice Fbase (x, t) (hdir, τ)) 0 := by
          simpa [directionalSlice] using hbase_at_line.comp 0 hpairLine3
        have haff3 : ContDiffAt ℝ 3 aff 0 := by
          simpa [aff, sub_eq_add_neg, smul_eq_mul, add_comm, add_left_comm, add_assoc] using
            (contDiffAt_const.add
              ((contDiffAt_id.smul contDiffAt_const).neg : ContDiffAt ℝ 3 (fun a : ℝ ↦ -(a • τ)) 0) :
                ContDiffAt ℝ 3 (fun a : ℝ ↦ (-t) + -(a • τ)) 0)
        have hlinear_second : iteratedDeriv 2 (fun a : ℝ ↦ a * τ) 0 = 0 := by
          calc
            iteratedDeriv 2 (fun a : ℝ ↦ a * τ) 0 = iteratedDeriv 2 (fun a : ℝ ↦ a) 0 * τ := by
              simpa using
                (iteratedDeriv_mul_const_field (f := fun a : ℝ ↦ a) (c := τ) (n := 2) (x := 0))
            _ = 0 := by
                  simp [iteratedDeriv_fun_id]
        have hlinear_third : iteratedDeriv 3 (fun a : ℝ ↦ a * τ) 0 = 0 := by
          calc
            iteratedDeriv 3 (fun a : ℝ ↦ a * τ) 0 = iteratedDeriv 3 (fun a : ℝ ↦ a) 0 * τ := by
              simpa using
                (iteratedDeriv_mul_const_field (f := fun a : ℝ ↦ a) (c := τ) (n := 3) (x := 0))
            _ = 0 := by
                  simp [iteratedDeriv_fun_id]
        have haff_second : iteratedDeriv 2 aff 0 = 0 := by
          calc
            iteratedDeriv 2 aff 0
                = iteratedDeriv 2 (fun a : ℝ ↦ -t) 0 - iteratedDeriv 2 (fun a : ℝ ↦ a * τ) 0 := by
                    simpa [aff] using
                      (iteratedDeriv_sub
                        (contDiffAt_const.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
                        (((contDiffAt_id.smul contDiffAt_const) :
                          ContDiffAt ℝ 3 (fun a : ℝ ↦ a • τ) 0).of_le
                          (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) :
                          iteratedDeriv 2 (fun a : ℝ ↦ (-t) - a * τ) 0 =
                            iteratedDeriv 2 (fun a : ℝ ↦ -t) 0 -
                              iteratedDeriv 2 (fun a : ℝ ↦ a * τ) 0)
            _ = 0 := by
                  rw [hlinear_second]
                  simp [iteratedDeriv_const]
        have haff_third : iteratedDeriv 3 aff 0 = 0 := by
          calc
            iteratedDeriv 3 aff 0
                = iteratedDeriv 3 (fun a : ℝ ↦ -t) 0 - iteratedDeriv 3 (fun a : ℝ ↦ a * τ) 0 := by
                    simpa [aff] using
                      (iteratedDeriv_sub
                        contDiffAt_const
                        ((contDiffAt_id.smul contDiffAt_const) :
                          ContDiffAt ℝ 3 (fun a : ℝ ↦ a • τ) 0) :
                          iteratedDeriv 3 (fun a : ℝ ↦ (-t) - a * τ) 0 =
                            iteratedDeriv 3 (fun a : ℝ ↦ -t) 0 -
                              iteratedDeriv 3 (fun a : ℝ ↦ a * τ) 0)
            _ = 0 := by
                  rw [hlinear_third]
                  simp [iteratedDeriv_const]
        have hslice_gap :
            directionalSlice gap (x, t) (hdir, τ) =
              directionalSlice Fbase (x, t) (hdir, τ) + aff := by
          funext a
          simp [gap, Fbase, Flin, aff, directionalSlice, sub_eq_add_neg, add_assoc, add_left_comm,
            add_comm, mul_comm, mul_left_comm, mul_assoc]
        have hsecond_eq :
            secondDirectionalDerivative gap (x, t) (hdir, τ) =
              secondDirectionalDerivative Fbase (x, t) (hdir, τ) := by
          rw [secondDirectionalDerivative, hslice_gap]
          calc
            iteratedDeriv 2 (directionalSlice Fbase (x, t) (hdir, τ) + aff) 0
                = iteratedDeriv 2 (directionalSlice Fbase (x, t) (hdir, τ)) 0 +
                    iteratedDeriv 2 aff 0 := by
                      simpa [Pi.add_apply] using
                        (iteratedDeriv_add
                          (n := 2)
                          (x := 0)
                          (f := directionalSlice Fbase (x, t) (hdir, τ))
                          (g := aff)
                          (hbase_slice3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
                          (haff3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)))
            _ = iteratedDeriv 2 (directionalSlice Fbase (x, t) (hdir, τ)) 0 := by
                  rw [haff_second]
                  simp
        have hthird_eq :
            thirdDirectionalDerivative gap (x, t) (hdir, τ) =
              thirdDirectionalDerivative Fbase (x, t) (hdir, τ) := by
          rw [thirdDirectionalDerivative, hslice_gap]
          calc
            iteratedDeriv 3 (directionalSlice Fbase (x, t) (hdir, τ) + aff) 0
                = iteratedDeriv 3 (directionalSlice Fbase (x, t) (hdir, τ)) 0 +
                    iteratedDeriv 3 aff 0 := by
                      simpa [Pi.add_apply] using
                        (iteratedDeriv_add
                          (n := 3)
                          (x := 0)
                          (f := directionalSlice Fbase (x, t) (hdir, τ))
                          (g := aff)
                          hbase_slice3
                          haff3)
            _ = iteratedDeriv 3 (directionalSlice Fbase (x, t) (hdir, τ)) 0 := by
                  rw [haff_third]
                  simp
        have hgap_at : ContDiffAt ℝ 2 gap (x, t) := by
          exact
            (hgap_contDiffOn.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).contDiffAt
              (hpull.isOpen_domain.mem_nhds hp)
        have hbase_at_two : ContDiffAt ℝ 2 Fbase (x, t) := by
          exact
            (hpull.contDiffOn.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).contDiffAt
              (hpull.isOpen_domain.mem_nhds hp)
        have hgap_diff : DifferentiableAt ℝ gap (x, t) := hgap_at.differentiableAt (by norm_num)
        have hbase_diff : DifferentiableAt ℝ Fbase (x, t) := hbase_at_two.differentiableAt (by norm_num)
        have hgap_grad : DifferentiableAt ℝ (∇ gap) (x, t) :=
          differentiableAt_gradient_of_contDiffAt_two hgap_at
        have hbase_grad : DifferentiableAt ℝ (∇ Fbase) (x, t) :=
          differentiableAt_gradient_of_contDiffAt_two hbase_at_two
        have hnorm_eq : ‖(hdir, τ)‖[gap; (x, t)] = ‖(hdir, τ)‖[Fbase; (x, t)] := by
          rw [hessianLocalNorm_def, hessianLocalNorm_def,
            ← secondDirectionalDerivative_eq_hessian_quadratic_form hgap_diff hgap_grad,
            hsecond_eq,
            secondDirectionalDerivative_eq_hessian_quadratic_form hbase_diff hbase_grad]
        calc
          |thirdDirectionalDerivative gap (x, t) (hdir, τ)|
              = |thirdDirectionalDerivative Fbase (x, t) (hdir, τ)| := by rw [hthird_eq]
          _ ≤ 2 * ‖(hdir, τ)‖[Fbase; (x, t)] ^ (3 : ℕ) := by
                simpa [one_mul] using hpull.third_deriv_bound hp (hdir, τ)
          _ = 2 * ‖(hdir, τ)‖[gap; (x, t)] ^ (3 : ℕ) := by rw [hnorm_eq]
          _ ≤ 2 * (1 : ℝ) * ‖(hdir, τ)‖[gap; (x, t)] ^ (3 : ℕ) := by
                simpa [one_mul]
      }
  simpa [strip, Fbase, Flin, gap, Pi.add_apply, sub_eq_add_neg, one_mul] using hgap_std

/-- Helper for Corollary 5.3.1: the raw strict epigraph is open because it is the strict
sublevel set `{gap < 0}` of the raw gap over the open strip `x ∈ dom`. -/
private theorem strictConstrainedEpigraph_isOpen
    {dom : Set E} {f : E → ℝ}
    (h : IsStandardSelfConcordantOn dom f) :
    IsOpen (strictConstrainedEpigraph dom f : Set (E × ℝ)) := by
  let strip : Set (E × ℝ) := {p : E × ℝ | p.1 ∈ dom}
  let gap : E × ℝ → ℝ := fun p ↦ f p.1 - p.2
  have hgap : IsStandardSelfConcordantOn strip gap := raw_gap_isStandardSelfConcordantOn h
  have hopen : IsOpen (strip ∩ gap ⁻¹' Set.Iio (0 : ℝ)) := by
    -- The raw gap is continuous on the open strip, so its strict sublevel is open there.
    exact hgap.contDiffOn.continuousOn.isOpen_inter_preimage hgap.isOpen_domain isOpen_Iio
  -- Rewrite the textbook strict epigraph as that strict sublevel set.
  convert hopen using 1
  ext p
  simp [strictConstrainedEpigraph, strip, gap, sub_lt_zero]

/-- Helper for Corollary 5.3.1: the raw strict epigraph is convex because it is the strict
sublevel set of the convex raw gap. -/
private theorem strictConstrainedEpigraph_isConvex
    {dom : Set E} {f : E → ℝ}
    (h : IsStandardSelfConcordantOn dom f) :
    Convex ℝ (strictConstrainedEpigraph dom f : Set (E × ℝ)) := by
  let strip : Set (E × ℝ) := {p : E × ℝ | p.1 ∈ dom}
  let gap : E × ℝ → ℝ := fun p ↦ f p.1 - p.2
  have hrepr :
      strictConstrainedEpigraph dom f = {p ∈ strip | gap p < (0 : ℝ)} := by
    -- Rewrite the source epigraph as the strict sublevel set of the raw gap.
    ext p
    simp [strictConstrainedEpigraph, strip, gap, sub_lt_zero]
  rw [hrepr]
  -- Convexity follows from the convex raw-gap owner on the strip.
  exact (raw_gap_isStandardSelfConcordantOn h).convexOn.convex_lt 0

/-- Helper for Corollary 5.3.1: the slack logarithmic term `p ↦ -log (p.2 - f p.1)` is `C³`
at every raw strict-epigraph point. -/
private theorem raw_slackBarrier_contDiffAt_three
    {dom : Set E} {f : E → ℝ} {p : E × ℝ}
    (h : IsStandardSelfConcordantOn dom f)
    (hp : p ∈ strictConstrainedEpigraph dom f) :
    ContDiffAt ℝ 3 (sublevelLogBarrier (fun q : E × ℝ ↦ f q.1 - q.2) 0) p := by
  let gap : E × ℝ → ℝ := fun q ↦ f q.1 - q.2
  have hp_strip : p ∈ {q : E × ℝ | q.1 ∈ dom} := by
    simpa [strictConstrainedEpigraph] using hp.1
  have hgap_cont :
      ContDiffAt ℝ 3 gap p := by
    let hgap : IsStandardSelfConcordantOn {q : E × ℝ | q.1 ∈ dom} gap :=
      raw_gap_isStandardSelfConcordantOn h
    -- Restrict the raw-gap `C³` owner to the current point.
    exact hgap.contDiffOn.contDiffAt (hgap.isOpen_domain.mem_nhds hp_strip)
  have hslack_pos : 0 < p.2 - f p.1 := sub_pos.mpr hp.2
  have hslack_cont :
      ContDiffAt ℝ 3 (fun q : E × ℝ ↦ q.2 - f q.1) p := by
    -- The slack is the negative raw gap, so it inherits the same regularity.
    simpa [gap, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hgap_cont.neg
  have hlog_cont :
      ContDiffAt ℝ 3 (fun q : E × ℝ ↦ Real.log (q.2 - f q.1)) p := by
    -- Compose the positive slack with `log`.
    exact (Real.contDiffAt_log.2 hslack_pos.ne').comp p hslack_cont
  -- Negating the logarithm recovers the standard sublevel barrier formula.
  convert hlog_cont.neg using 1
  ext q
  simp [sublevelLogBarrier, gap, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- Helper for Corollary 5.3.1: along a raw line `(x, t) + a • (h, τ)`, the epigraph barrier
has the normalized slack form used in the source proof. -/
private theorem epigraphLogBarrier_directionalSlice_eq_slack_form
    {f : E → ℝ} (x h : E) (t τ : ℝ) :
    directionalSlice (epigraphLogBarrier f) (x, t) (h, τ) =
      fun a : ℝ ↦
        (directionalSlice f x h a - a * τ) + a * τ -
          Real.log (t - (directionalSlice f x h a - a * τ)) := by
  -- Expand the pair slice and rewrite the logarithmic slack into the normalized source form.
  funext a
  simp [directionalSlice, epigraphLogBarrier_apply, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Corollary 5.3.1: subtracting the explicit affine correction `a * τ` from the
normalized slice shifts only the first derivative; the second and third iterated derivatives stay
equal to the base Chapter 5 directional derivatives. -/
private theorem normalized_slack_slice_derivative_data
    {dom : Set E} {f : E → ℝ}
    (h : IsStandardSelfConcordantOn dom f) {x : E} (hx : x ∈ dom) (u : E) (τ : ℝ) :
    deriv (fun a : ℝ ↦ directionalSlice f x u a - a * τ) 0 =
        inner ℝ (∇ f x) u - τ ∧
      iteratedDeriv 2 (fun a : ℝ ↦ directionalSlice f x u a - a * τ) 0 =
        secondDirectionalDerivative f x u ∧
      iteratedDeriv 3 (fun a : ℝ ↦ directionalSlice f x u a - a * τ) 0 =
        thirdDirectionalDerivative f x u := by
  have hfx3 : ContDiffAt ℝ 3 f x := h.contDiffOn.contDiffAt (h.isOpen_domain.mem_nhds hx)
  have hline3 : ContDiffAt ℝ 3 (fun a : ℝ ↦ x + a • u) 0 := by
    simpa using
      (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const) :
        ContDiffAt ℝ 3 (fun a : ℝ ↦ x + a • u) 0)
  have hslice3 : ContDiffAt ℝ 3 (directionalSlice f x u) 0 := by
    -- Restrict the ambient `C³` owner of `f` to the affine line through `x` in direction `u`.
    have hfx3_line : ContDiffAt ℝ 3 f ((fun a : ℝ ↦ x + a • u) 0) := by
      simpa using hfx3
    simpa [directionalSlice] using hfx3_line.comp 0 hline3
  have hlin3 : ContDiffAt ℝ 3 (fun a : ℝ ↦ a * τ) 0 := by
    -- The affine correction is polynomial, so its higher iterated derivatives vanish.
    simpa [smul_eq_mul] using
      (contDiffAt_id.smul contDiffAt_const : ContDiffAt ℝ 3 (fun a : ℝ ↦ a • τ) 0)
  have hslice_diff : DifferentiableAt ℝ (directionalSlice f x u) 0 :=
    hslice3.differentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  have hlin_diff : DifferentiableAt ℝ (fun a : ℝ ↦ a * τ) 0 :=
    hlin3.differentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  have hslice_deriv :
      deriv (directionalSlice f x u) 0 = inner ℝ (∇ f x) u := by
    have hfx1 : DifferentiableAt ℝ f x :=
      hfx3.differentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
    -- Rewrite the slice derivative through the Chapter 1 gradient pairing owner.
    calc
      deriv (directionalSlice f x u) 0 = lineDeriv ℝ f x u := rfl
      _ = fderiv ℝ f x u := hfx1.lineDeriv_eq_fderiv
      _ = inner ℝ (∇ f x) u := by
            rw [← inner_gradient_left hfx1]
  have hlin_deriv : deriv (fun a : ℝ ↦ a * τ) 0 = τ := by
    simpa using (deriv_mul_const_field (u := fun a : ℝ ↦ a) (v := τ) (x := 0))
  have hderiv_sub :
      deriv (fun a : ℝ ↦ directionalSlice f x u a - a * τ) 0 =
        deriv (directionalSlice f x u) 0 - deriv (fun a : ℝ ↦ a * τ) 0 := by
    simpa using
      (deriv_sub hslice_diff hlin_diff :
        deriv (directionalSlice f x u - fun a : ℝ ↦ a * τ) 0 =
          deriv (directionalSlice f x u) 0 - deriv (fun a : ℝ ↦ a * τ) 0)
  have hsecond_sub :
      iteratedDeriv 2 (fun a : ℝ ↦ directionalSlice f x u a - a * τ) 0 =
        iteratedDeriv 2 (directionalSlice f x u) 0 -
          iteratedDeriv 2 (fun a : ℝ ↦ a * τ) 0 := by
    simpa using
      (iteratedDeriv_sub
        (hslice3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
        (hlin3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) :
        iteratedDeriv 2 (directionalSlice f x u - fun a : ℝ ↦ a * τ) 0 =
          iteratedDeriv 2 (directionalSlice f x u) 0 -
            iteratedDeriv 2 (fun a : ℝ ↦ a * τ) 0)
  have hthird_sub :
      iteratedDeriv 3 (fun a : ℝ ↦ directionalSlice f x u a - a * τ) 0 =
        iteratedDeriv 3 (directionalSlice f x u) 0 -
          iteratedDeriv 3 (fun a : ℝ ↦ a * τ) 0 := by
    simpa using
      (iteratedDeriv_sub hslice3 hlin3 :
        iteratedDeriv 3 (directionalSlice f x u - fun a : ℝ ↦ a * τ) 0 =
          iteratedDeriv 3 (directionalSlice f x u) 0 -
            iteratedDeriv 3 (fun a : ℝ ↦ a * τ) 0)
  have hlin_second : iteratedDeriv 2 (fun a : ℝ ↦ a * τ) 0 = 0 := by
    calc
      iteratedDeriv 2 (fun a : ℝ ↦ a * τ) 0 = iteratedDeriv 2 (fun a : ℝ ↦ a) 0 * τ := by
        simpa using
          (iteratedDeriv_mul_const_field (f := fun a : ℝ ↦ a) (c := τ) (n := 2) (x := 0))
      _ = 0 := by
        simp [iteratedDeriv_fun_id]
  have hlin_third : iteratedDeriv 3 (fun a : ℝ ↦ a * τ) 0 = 0 := by
    calc
      iteratedDeriv 3 (fun a : ℝ ↦ a * τ) 0 = iteratedDeriv 3 (fun a : ℝ ↦ a) 0 * τ := by
        simpa using
          (iteratedDeriv_mul_const_field (f := fun a : ℝ ↦ a) (c := τ) (n := 3) (x := 0))
      _ = 0 := by
        simp [iteratedDeriv_fun_id]
  constructor
  · -- The affine correction contributes only `-τ` to the first derivative.
    rw [hderiv_sub, hslice_deriv, hlin_deriv]
  constructor
  · -- From second order onward, the affine correction has zero contribution.
    rw [hsecond_sub, hlin_second]
    simp [secondDirectionalDerivative]
  · -- The same vanishing persists at third order.
    rw [hthird_sub, hlin_third]
    simp [thirdDirectionalDerivative]

/-- Helper for Corollary 5.3.1: the normalized source slice
`a ↦ directionalSlice f x u a - a * τ` is `C³` at the base point. -/
private theorem normalized_slack_slice_contDiffAt_three
    {dom : Set E} {f : E → ℝ}
    (h : IsStandardSelfConcordantOn dom f) {x : E} (hx : x ∈ dom) (u : E) (τ : ℝ) :
    ContDiffAt ℝ 3 (fun a : ℝ ↦ directionalSlice f x u a - a * τ) 0 := by
  have hfx3 : ContDiffAt ℝ 3 f x := h.contDiffOn.contDiffAt (h.isOpen_domain.mem_nhds hx)
  have hline3 : ContDiffAt ℝ 3 (fun a : ℝ ↦ x + a • u) 0 := by
    simpa using
      (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const) :
        ContDiffAt ℝ 3 (fun a : ℝ ↦ x + a • u) 0)
  have hslice3 : ContDiffAt ℝ 3 (directionalSlice f x u) 0 := by
    -- Restrict the ambient `C³` owner of `f` to the affine line through `x` in direction `u`.
    have hfx3_line : ContDiffAt ℝ 3 f ((fun a : ℝ ↦ x + a • u) 0) := by
      simpa using hfx3
    simpa [directionalSlice] using hfx3_line.comp 0 hline3
  have hlin3 : ContDiffAt ℝ 3 (fun a : ℝ ↦ a * τ) 0 := by
    -- The explicit affine correction is polynomial, so it is `C³` automatically.
    simpa [smul_eq_mul] using
      (contDiffAt_id.smul contDiffAt_const : ContDiffAt ℝ 3 (fun a : ℝ ↦ a • τ) 0)
  -- The normalized slice is the source slice minus the affine correction.
  simpa using hslice3.sub hlin3

/-- Helper for Corollary 5.3.1: the base self-concordance data for `f` can be rewritten in the
scalar form `0 ≤ b` and `|c| ≤ 2 * (sqrt b)^3`. -/
private theorem base_directional_data_sqrt_form
    {dom : Set E} {f : E → ℝ}
    (h : IsStandardSelfConcordantOn dom f) {x : E} (hx : x ∈ dom) (u : E) :
    0 ≤ secondDirectionalDerivative f x u ∧
      |thirdDirectionalDerivative f x u| ≤
        2 * (Real.sqrt (secondDirectionalDerivative f x u)) ^ (3 : ℕ) := by
  have hfx3 : ContDiffAt ℝ 3 f x := h.contDiffOn.contDiffAt (h.isOpen_domain.mem_nhds hx)
  have hfx2 : ContDiffAt ℝ 2 f x := hfx3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hdiff : DifferentiableAt ℝ f x := hfx3.differentiableAt (by norm_num)
  have hgrad : DifferentiableAt ℝ (∇ f) x := differentiableAt_gradient_of_contDiffAt_two hfx2
  have hsecond_eq :
      secondDirectionalDerivative f x u = inner ℝ u (hessian f x u) :=
    secondDirectionalDerivative_eq_hessian_quadratic_form hdiff hgrad
  have hsecond_nonneg : 0 ≤ secondDirectionalDerivative f x u := by
    -- Rewrite the second directional derivative as the Hessian quadratic form and use
    -- pointwise Hessian positive semidefiniteness on the domain.
    rw [hsecond_eq]
    exact h.hessian_posSemidef hx u
  constructor
  · exact hsecond_nonneg
  · -- Replace the Hessian local norm by the square root of the second directional derivative.
    calc
      |thirdDirectionalDerivative f x u|
          ≤ 2 * ‖u‖[f; x] ^ (3 : ℕ) := by
            simpa [one_mul] using h.third_deriv_bound hx u
      _ = 2 * (Real.sqrt (inner ℝ u (hessian f x u))) ^ (3 : ℕ) := by
            rw [hessianLocalNorm_def]
      _ = 2 * (Real.sqrt (secondDirectionalDerivative f x u)) ^ (3 : ℕ) := by
            rw [hsecond_eq]

/-- Helper for Corollary 5.3.1: composing `-log` with a positive scalar slack slice gives the
expected second iterated derivative at the base point. -/
private theorem negLog_comp_iteratedDeriv_two
    {σ : ℝ → ℝ} {s delta b : ℝ}
    (hσ3 : ContDiffAt ℝ 3 σ 0)
    (hσ0 : σ 0 = s)
    (hs : 0 < s)
    (hσ_deriv : deriv σ 0 = delta)
    (hσ_second : iteratedDeriv 2 σ 0 = -b) :
    iteratedDeriv 2 (fun a : ℝ ↦ -Real.log (σ a)) 0 =
      b / s + delta ^ (2 : ℕ) / s ^ (2 : ℕ) := by
  have hlog_cont : ContDiffAt ℝ 3 Real.log (σ 0) := by
    -- Positivity of the slack keeps the logarithm away from its singularity.
    simpa [hσ0] using (Real.contDiffAt_log.2 hs.ne')
  have hderiv_log : deriv Real.log = fun y : ℝ ↦ y⁻¹ := by
    -- Differentiate the logarithm once so the chain rule has explicit coefficients.
    ext y
    rw [Real.deriv_log]
  have hsecond_log :
      iteratedDeriv 2 Real.log s = -(s ^ (2 : ℕ))⁻¹ := by
    -- The second derivative of `log` is the negative inverse square.
    calc
      iteratedDeriv 2 Real.log s = deriv (deriv Real.log) s := by
              simp [iteratedDeriv_succ]
      _ = deriv (fun y : ℝ ↦ y⁻¹) s := by
            rw [hderiv_log]
      _ = -(s ^ (2 : ℕ))⁻¹ := by
            rw [deriv_inv]
  have hcomp_two :
      iteratedDeriv 2 (fun a : ℝ ↦ Real.log (σ a)) 0 =
        iteratedDeriv 2 Real.log (σ 0) * deriv σ 0 ^ (2 : ℕ) +
          deriv Real.log (σ 0) * iteratedDeriv 2 σ 0 := by
    -- Apply the scalar second-order chain rule to the slack slice.
    simpa [Function.comp] using
      (iteratedDeriv_comp_two
        (g := Real.log)
        (f := σ)
        (x := 0)
        (hlog_cont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
        (hσ3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)))
  calc
    iteratedDeriv 2 (fun a : ℝ ↦ -Real.log (σ a)) 0
        = -iteratedDeriv 2 (fun a : ℝ ↦ Real.log (σ a)) 0 := by
            simp
    _ = -(iteratedDeriv 2 Real.log (σ 0) * deriv σ 0 ^ (2 : ℕ) +
            deriv Real.log (σ 0) * iteratedDeriv 2 σ 0) := by
          rw [hcomp_two]
    _ = -(-(s ^ (2 : ℕ))⁻¹ * delta ^ (2 : ℕ) + s⁻¹ * (-b)) := by
          rw [hσ0, hsecond_log, hderiv_log, hσ_deriv, hσ_second]
    _ = b / s + delta ^ (2 : ℕ) / s ^ (2 : ℕ) := by
          field_simp [hs.ne']
          ring

/-- Helper for Corollary 5.3.1: composing `-log` with a positive scalar slack slice gives the
expected third iterated derivative at the base point. -/
private theorem negLog_comp_iteratedDeriv_three
    {σ : ℝ → ℝ} {s delta b c : ℝ}
    (hσ3 : ContDiffAt ℝ 3 σ 0)
    (hσ0 : σ 0 = s)
    (hs : 0 < s)
    (hσ_deriv : deriv σ 0 = delta)
    (hσ_second : iteratedDeriv 2 σ 0 = -b)
    (hσ_third : iteratedDeriv 3 σ 0 = -c) :
    iteratedDeriv 3 (fun a : ℝ ↦ -Real.log (σ a)) 0 =
      c / s - 3 * b * delta / s ^ (2 : ℕ) - 2 * delta ^ (3 : ℕ) / s ^ (3 : ℕ) := by
  have hlog_cont : ContDiffAt ℝ 3 Real.log (σ 0) := by
    -- Positivity of the slack keeps the logarithm away from its singularity.
    simpa [hσ0] using (Real.contDiffAt_log.2 hs.ne')
  have hderiv_log : deriv Real.log = fun y : ℝ ↦ y⁻¹ := by
    -- Differentiate the logarithm once so the chain rule has explicit coefficients.
    ext y
    rw [Real.deriv_log]
  have hsecond_log :
      iteratedDeriv 2 Real.log s = -(s ^ (2 : ℕ))⁻¹ := by
    -- The second derivative of `log` is the negative inverse square.
    calc
      iteratedDeriv 2 Real.log s = deriv (deriv Real.log) s := by
              simp [iteratedDeriv_succ]
      _ = deriv (fun y : ℝ ↦ y⁻¹) s := by
            rw [hderiv_log]
      _ = -(s ^ (2 : ℕ))⁻¹ := by
            rw [deriv_inv]
  have hthird_log :
      iteratedDeriv 3 Real.log s = 2 * (s ^ (3 : ℕ))⁻¹ := by
    -- The third derivative of `log` is the positive inverse cube with coefficient `2`.
    calc
      iteratedDeriv 3 Real.log s = iteratedDeriv 2 (deriv Real.log) s := by
              simp [iteratedDeriv_succ']
      _ = iteratedDeriv 2 (fun y : ℝ ↦ y⁻¹) s := by
            rw [hderiv_log]
      _ = deriv^[2] Inv.inv s := by
            rw [iteratedDeriv_eq_iterate]
      _ = 2 * s ^ (-3 : ℤ) := by
            simpa using iter_deriv_inv 2 s
      _ = 2 * (s ^ (3 : ℕ))⁻¹ := by
            rw [zpow_neg]
            field_simp [hs.ne']
  have hcomp_three :
      iteratedDeriv 3 (fun a : ℝ ↦ Real.log (σ a)) 0 =
        iteratedDeriv 3 Real.log (σ 0) * deriv σ 0 ^ (3 : ℕ) +
          3 * iteratedDeriv 2 Real.log (σ 0) * iteratedDeriv 2 σ 0 * deriv σ 0 +
          deriv Real.log (σ 0) * iteratedDeriv 3 σ 0 := by
    -- Apply the scalar third-order chain rule to the slack slice.
    simpa [Function.comp] using
      (iteratedDeriv_comp_three
        (g := Real.log)
        (f := σ)
        (x := 0)
        hlog_cont
        hσ3)
  calc
    iteratedDeriv 3 (fun a : ℝ ↦ -Real.log (σ a)) 0
        = -iteratedDeriv 3 (fun a : ℝ ↦ Real.log (σ a)) 0 := by
            simp
    _ = -(iteratedDeriv 3 Real.log (σ 0) * deriv σ 0 ^ (3 : ℕ) +
            3 * iteratedDeriv 2 Real.log (σ 0) * iteratedDeriv 2 σ 0 * deriv σ 0 +
            deriv Real.log (σ 0) * iteratedDeriv 3 σ 0) := by
          rw [hcomp_three]
    _ = -(2 * (s ^ (3 : ℕ))⁻¹ * delta ^ (3 : ℕ) +
            3 * (-(s ^ (2 : ℕ))⁻¹) * (-b) * delta +
            s⁻¹ * (-c)) := by
          rw [hσ0, hthird_log, hsecond_log, hderiv_log, hσ_deriv, hσ_second, hσ_third]
    _ = c / s - 3 * b * delta / s ^ (2 : ℕ) - 2 * delta ^ (3 : ℕ) / s ^ (3 : ℕ) := by
          field_simp [hs.ne']
          ring

/-- Helper for Corollary 5.3.1: the normalized positive cubic expression is controlled by the
cube of the total square-root sum. -/
private theorem normalized_cubic_positive_bound
    {a b u : ℝ}
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hu : 0 ≤ u) :
    2 * (Real.sqrt a) ^ (3 : ℕ) + 3 * Real.sqrt a * b + 3 * u * b + 2 * u ^ (3 : ℕ) ≤
      2 * (Real.sqrt (a + b + u ^ (2 : ℕ))) ^ (3 : ℕ) := by
  let p := Real.sqrt a
  let s := a + b + u ^ (2 : ℕ)
  let t := p + u
  let r := Real.sqrt s
  have hp : 0 ≤ p := by
    exact Real.sqrt_nonneg a
  have hs : 0 ≤ s := by
    dsimp [s]
    nlinarith
  have hr : 0 ≤ r := by
    dsimp [r]
    exact Real.sqrt_nonneg s
  have hs_eq : s = p ^ (2 : ℕ) + b + u ^ (2 : ℕ) := by
    -- Rewrite the total second-order term in the variables `p = sqrt a` and `u`.
    have ha_sq : a = p ^ (2 : ℕ) := by
      dsimp [p]
      symm
      simpa using Real.sq_sqrt ha
    dsimp [s]
    nlinarith [ha_sq]
  have ht_eq :
      t * (3 * s - t ^ (2 : ℕ)) =
        2 * p ^ (3 : ℕ) + 3 * p * b + 3 * b * u + 2 * u ^ (3 : ℕ) := by
    -- The normalized cubic expression factors through the standard scalar identity.
    dsimp [t]
    rw [hs_eq]
    ring
  have hr_sq : r ^ (2 : ℕ) = s := by
    dsimp [r]
    simpa using Real.sq_sqrt hs
  have hfactor :
      2 * r ^ (3 : ℕ) - t * (3 * s - t ^ (2 : ℕ)) =
        (r - t) ^ (2 : ℕ) * (2 * r + t) := by
    -- Factoring against `sqrt s` produces a manifestly nonnegative remainder.
    rw [← hr_sq]
    ring
  have hfactor_nonneg :
      0 ≤ (r - t) ^ (2 : ℕ) * (2 * r + t) := by
    refine mul_nonneg (sq_nonneg _) ?_
    nlinarith [hr, hp, hu]
  have hbase : t * (3 * s - t ^ (2 : ℕ)) ≤ 2 * r ^ (3 : ℕ) := by
    nlinarith [hfactor_nonneg, hfactor]
  calc
    2 * (Real.sqrt a) ^ (3 : ℕ) + 3 * Real.sqrt a * b + 3 * u * b + 2 * u ^ (3 : ℕ)
        = 2 * p ^ (3 : ℕ) + 3 * p * b + 3 * b * u + 2 * u ^ (3 : ℕ) := by
            dsimp [p]
            ring
    _ = t * (3 * s - t ^ (2 : ℕ)) := by
          rw [ht_eq]
    _ ≤ 2 * r ^ (3 : ℕ) := hbase
    _ = 2 * (Real.sqrt (a + b + u ^ (2 : ℕ))) ^ (3 : ℕ) := by
          dsimp [r, s]

/-- Helper for Corollary 5.3.1: after normalizing the strict slack by
`λ = 1 / s` and `q = delta / s`, the epigraph cubic estimate reduces to a scalar merge
inequality. -/
private theorem epigraph_scalar_cubic_merge
    {b c lam q : ℝ}
    (hb : 0 ≤ b)
    (hlam : 0 ≤ lam)
    (hc : |c| ≤ 2 * (Real.sqrt b) ^ (3 : ℕ)) :
    |(1 + lam) * c - 3 * lam * b * q - 2 * q ^ (3 : ℕ)| ≤
      2 * (Real.sqrt (b + lam * b + q ^ (2 : ℕ))) ^ (3 : ℕ) := by
  have htri :
      |(1 + lam) * c - 3 * lam * b * q - 2 * q ^ (3 : ℕ)| ≤
        |(1 + lam) * c| + |3 * lam * b * q| + |2 * q ^ (3 : ℕ)| := by
    -- Use the triangle inequality twice to separate the three normalized cubic pieces.
    have houter :
        |((1 + lam) * c - 3 * lam * b * q) - 2 * q ^ (3 : ℕ)| ≤
          |(1 + lam) * c - 3 * lam * b * q| + |2 * q ^ (3 : ℕ)| := by
      simpa [sub_eq_add_neg] using
        (abs_sub_le ((1 + lam) * c - 3 * lam * b * q) 0 (2 * q ^ (3 : ℕ)))
    have hinner :
        |(1 + lam) * c - 3 * lam * b * q| ≤ |(1 + lam) * c| + |3 * lam * b * q| := by
      simpa [sub_eq_add_neg] using (abs_sub_le ((1 + lam) * c) 0 (3 * lam * b * q))
    nlinarith
  have hfirst_abs : |(1 + lam) * c| = (1 + lam) * |c| := by
    -- The prefactor `1 + lam` is nonnegative.
    rw [abs_mul, abs_of_nonneg (by linarith [hlam])]
  have hsecond_abs : |3 * lam * b * q| = 3 * lam * b * |q| := by
    -- Only the `q` factor contributes an absolute value.
    calc
      |3 * lam * b * q| = |3| * |lam| * |b| * |q| := by
        rw [abs_mul, abs_mul, abs_mul]
      _ = 3 * lam * b * |q| := by
        rw [abs_of_nonneg (by positivity), abs_of_nonneg hlam, abs_of_nonneg hb]
  have hthird_abs : |2 * q ^ (3 : ℕ)| = 2 * |q| ^ (3 : ℕ) := by
    -- The odd power keeps only the absolute value of `q`.
    calc
      |2 * q ^ (3 : ℕ)| = |2| * |q ^ (3 : ℕ)| := by
        rw [abs_mul]
      _ = 2 * |q| ^ (3 : ℕ) := by
        simp [abs_pow]
  let p := Real.sqrt b
  have hp : 0 ≤ p := by
    exact Real.sqrt_nonneg b
  have hb_sq : b = p ^ (2 : ℕ) := by
    dsimp [p]
    symm
    simpa using Real.sq_sqrt hb
  have hscaled_c :
      (1 + lam) * |c| ≤ 2 * (1 + lam) * p ^ (3 : ℕ) := by
    -- Scale the base cubic estimate by the nonnegative factor `1 + lam`.
    have : (1 + lam) * |c| ≤ (1 + lam) * (2 * (Real.sqrt b) ^ (3 : ℕ)) := by
      nlinarith [hc]
    simpa [p, mul_assoc, mul_left_comm, mul_comm] using this
  have hfirst_compare :
      2 * (1 + lam) * p ^ (3 : ℕ) ≤ 2 * p ^ (3 : ℕ) + 3 * p * (lam * b) := by
    -- The extra factor `lam` is absorbed into the positive `3 * p * (lam * b)` term.
    calc
      2 * (1 + lam) * p ^ (3 : ℕ) ≤ 2 * p ^ (3 : ℕ) + 3 * lam * p ^ (3 : ℕ) := by
            nlinarith [pow_nonneg hp 3]
      _ = 2 * p ^ (3 : ℕ) + 3 * p * (lam * b) := by
            rw [hb_sq]
            ring
  have hpositive :
      2 * (Real.sqrt b) ^ (3 : ℕ) + 3 * Real.sqrt b * (lam * b) +
          3 * |q| * (lam * b) + 2 * |q| ^ (3 : ℕ) ≤
        2 * (Real.sqrt (b + lam * b + |q| ^ (2 : ℕ))) ^ (3 : ℕ) := by
    -- This is the normalized positive cubic bound from the source factorization.
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      normalized_cubic_positive_bound
        (a := b)
        (b := lam * b)
        (u := |q|)
        hb
        (mul_nonneg hlam hb)
        (abs_nonneg q)
  have hsum :
      (1 + lam) * |c| + 3 * lam * b * |q| + 2 * |q| ^ (3 : ℕ) ≤
        2 * (Real.sqrt b) ^ (3 : ℕ) + 3 * Real.sqrt b * (lam * b) +
          3 * |q| * (lam * b) + 2 * |q| ^ (3 : ℕ) := by
    -- Replace the scaled `|c|` term by the positive expression handled by the factorization.
    have hcompare :
        2 * (1 + lam) * p ^ (3 : ℕ) + 3 * lam * b * |q| + 2 * |q| ^ (3 : ℕ) ≤
          2 * p ^ (3 : ℕ) + 3 * p * (lam * b) + 3 * |q| * (lam * b) + 2 * |q| ^ (3 : ℕ) := by
      nlinarith [hfirst_compare]
    nlinarith [hscaled_c, hcompare]
  calc
    |(1 + lam) * c - 3 * lam * b * q - 2 * q ^ (3 : ℕ)|
        ≤ |(1 + lam) * c| + |3 * lam * b * q| + |2 * q ^ (3 : ℕ)| := htri
    _ = (1 + lam) * |c| + 3 * lam * b * |q| + 2 * |q| ^ (3 : ℕ) := by
          rw [hfirst_abs, hsecond_abs, hthird_abs]
    _ ≤ 2 * (Real.sqrt b) ^ (3 : ℕ) + 3 * Real.sqrt b * (lam * b) +
          3 * |q| * (lam * b) + 2 * |q| ^ (3 : ℕ) := hsum
    _ ≤ 2 * (Real.sqrt (b + lam * b + |q| ^ (2 : ℕ))) ^ (3 : ℕ) := hpositive
    _ = 2 * (Real.sqrt (b + lam * b + q ^ (2 : ℕ))) ^ (3 : ℕ) := by
          rw [sq_abs]

/-- Helper for Corollary 5.3.1: once the normalized second- and third-derivative formulas for the
epigraph slice are available, the final Chapter 5 cubic estimate is the standard rewrite of the
Hessian local norm through the second directional derivative. -/
private theorem epigraph_third_deriv_bound_of_normalized_data
    {f : E → ℝ} {x hdir : E} {t τ second third : ℝ}
    (hcont : ContDiffAt ℝ 3 (epigraphLogBarrier f) (x, t))
    (hsecond :
      secondDirectionalDerivative (epigraphLogBarrier f) (x, t) (hdir, τ) = second)
    (hthird :
      thirdDirectionalDerivative (epigraphLogBarrier f) (x, t) (hdir, τ) = third)
    (hscalar : |third| ≤ 2 * (Real.sqrt second) ^ (3 : ℕ)) :
    |thirdDirectionalDerivative (epigraphLogBarrier f) (x, t) (hdir, τ)| ≤
      2 * ‖(hdir, τ)‖[epigraphLogBarrier f; (x, t)] ^ (3 : ℕ) := by
  have hcont2 : ContDiffAt ℝ 2 (epigraphLogBarrier f) (x, t) :=
    hcont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hdiff : DifferentiableAt ℝ (epigraphLogBarrier f) (x, t) :=
    hcont.differentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  have hgrad : DifferentiableAt ℝ (∇ (epigraphLogBarrier f)) (x, t) :=
    differentiableAt_gradient_of_contDiffAt_two hcont2
  have hquad :
      inner ℝ (hdir, τ) (hessian (epigraphLogBarrier f) (x, t) (hdir, τ)) = second := by
    -- Rewrite the local quadratic form by the owner-level second directional derivative bridge.
    calc
      inner ℝ (hdir, τ) (hessian (epigraphLogBarrier f) (x, t) (hdir, τ))
          = secondDirectionalDerivative (epigraphLogBarrier f) (x, t) (hdir, τ) := by
              symm
              exact secondDirectionalDerivative_eq_hessian_quadratic_form hdiff hgrad
      _ = second := hsecond
  calc
    |thirdDirectionalDerivative (epigraphLogBarrier f) (x, t) (hdir, τ)| = |third| := by
      rw [hthird]
    _ ≤ 2 * (Real.sqrt second) ^ (3 : ℕ) := hscalar
    _ = 2 * (Real.sqrt (inner ℝ (hdir, τ)
          (hessian (epigraphLogBarrier f) (x, t) (hdir, τ)))) ^ (3 : ℕ) := by
          rw [← hquad]
    _ = 2 * ‖(hdir, τ)‖[epigraphLogBarrier f; (x, t)] ^ (3 : ℕ) := by
          rw [hessianLocalNorm_def]

/-- Helper for Corollary 5.3.1: the remaining source-faithful blocker is the cubic directional
derivative estimate for the raw epigraph barrier. -/
private theorem raw_epigraphLogBarrier_third_deriv_bound
    {dom : Set E} {f : E → ℝ}
    (h : IsStandardSelfConcordantOn dom f)
    {p : E × ℝ} (hp : p ∈ strictConstrainedEpigraph dom f) (u : E × ℝ) :
    |thirdDirectionalDerivative (epigraphLogBarrier f) p u| ≤
      2 * ‖u‖[epigraphLogBarrier f; p] ^ (3 : ℕ) := by
  rcases p with ⟨x, t⟩
  rcases u with ⟨hdir, τ⟩
  have hp_raw : x ∈ dom ∧ f x < t := by
    simpa [strictConstrainedEpigraph] using hp
  have hs : 0 < t - f x := sub_pos.mpr hp_raw.2
  have hslice_data :
      deriv (fun a : ℝ ↦ directionalSlice f x hdir a - a * τ) 0 =
          inner ℝ (∇ f x) hdir - τ ∧
        iteratedDeriv 2 (fun a : ℝ ↦ directionalSlice f x hdir a - a * τ) 0 =
          secondDirectionalDerivative f x hdir ∧
        iteratedDeriv 3 (fun a : ℝ ↦ directionalSlice f x hdir a - a * τ) 0 =
          thirdDirectionalDerivative f x hdir :=
    normalized_slack_slice_derivative_data h hp_raw.1 hdir τ
  let s : ℝ := t - f x
  let delta : ℝ := τ - inner ℝ (∇ f x) hdir
  let b : ℝ := secondDirectionalDerivative f x hdir
  let c : ℝ := thirdDirectionalDerivative f x hdir
  let ψ : ℝ → ℝ := fun a : ℝ ↦ directionalSlice f x hdir a - a * τ
  let σ : ℝ → ℝ := fun a : ℝ ↦ t - ψ a
  have hs' : 0 < s := by
    simpa [s] using hs
  have hpsi_deriv : deriv ψ 0 = -delta := by
    -- The affine correction shifts only the first derivative by `-τ`.
    simpa [ψ, delta, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hslice_data.1
  have hpsi_second : iteratedDeriv 2 ψ 0 = b := by
    -- The second derivative of the normalized slice is the base directional second derivative.
    simpa [ψ, b] using hslice_data.2.1
  have hpsi_third : iteratedDeriv 3 ψ 0 = c := by
    -- The third derivative of the normalized slice is the base directional third derivative.
    simpa [ψ, c] using hslice_data.2.2
  have hpsi3 : ContDiffAt ℝ 3 ψ 0 := by
    -- The normalized source slice is already `C³` at the base point.
    simpa [ψ] using normalized_slack_slice_contDiffAt_three h hp_raw.1 hdir τ
  have hbase_data :
      0 ≤ b ∧ |c| ≤ 2 * (Real.sqrt b) ^ (3 : ℕ) := by
    -- Rewrite the base self-concordance inequality into the scalar `(b, c)` notation.
    simpa [b, c] using base_directional_data_sqrt_form h hp_raw.1 hdir
  have hsigma_zero : σ 0 = s := by
    -- The normalized slack starts at the geometric slack `s = t - f x`.
    simp [σ, ψ, s, directionalSlice]
  have hsigma3 : ContDiffAt ℝ 3 σ 0 := by
    -- The slack slice is the constant `t` minus the normalized source slice.
    simpa [σ] using (contDiffAt_const.sub hpsi3)
  have hpsi_diff : DifferentiableAt ℝ ψ 0 :=
    hpsi3.differentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  have hsigma_deriv : deriv σ 0 = delta := by
    -- Differentiating `σ = t - ψ` flips the sign of the normalized first derivative.
    have hconst_diff : DifferentiableAt ℝ (fun a : ℝ ↦ t) 0 := by
      simpa using (differentiableAt_const : DifferentiableAt ℝ (fun a : ℝ ↦ t) 0)
    calc
      deriv σ 0 = deriv (fun a : ℝ ↦ t) 0 - deriv ψ 0 := by
        simpa [σ] using
          (deriv_sub
            hconst_diff
            hpsi_diff :
            deriv (fun a : ℝ ↦ t - ψ a) 0 = deriv (fun a : ℝ ↦ t) 0 - deriv ψ 0)
      _ = delta := by
            rw [hpsi_deriv]
            simp [delta]
  have hsigma_second : iteratedDeriv 2 σ 0 = -b := by
    -- From second order onward, `σ` is just the negated normalized slice.
    calc
      iteratedDeriv 2 σ 0 = iteratedDeriv 2 (fun a : ℝ ↦ t) 0 - iteratedDeriv 2 ψ 0 := by
        simpa [σ] using
          (iteratedDeriv_sub
            (contDiffAt_const.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
            (hpsi3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) :
              iteratedDeriv 2 (fun a : ℝ ↦ t - ψ a) 0 =
                iteratedDeriv 2 (fun a : ℝ ↦ t) 0 - iteratedDeriv 2 ψ 0)
      _ = -b := by
            rw [hpsi_second]
            simp [iteratedDeriv_const]
  have hsigma_third : iteratedDeriv 3 σ 0 = -c := by
    -- The same sign flip persists at third order.
    calc
      iteratedDeriv 3 σ 0 = iteratedDeriv 3 (fun a : ℝ ↦ t) 0 - iteratedDeriv 3 ψ 0 := by
        simpa [σ] using
          (iteratedDeriv_sub contDiffAt_const hpsi3 :
              iteratedDeriv 3 (fun a : ℝ ↦ t - ψ a) 0 =
                iteratedDeriv 3 (fun a : ℝ ↦ t) 0 - iteratedDeriv 3 ψ 0)
      _ = -c := by
            rw [hpsi_third]
            simp [iteratedDeriv_const]
  have hsigma_pos : 0 < σ 0 := by
    -- At the base point the normalized slack is the positive geometric slack.
    simpa [hsigma_zero] using hs'
  have hneglog3 : ContDiffAt ℝ 3 (fun a : ℝ ↦ -Real.log (σ a)) 0 := by
    -- Compose the positive slack slice with the scalar logarithmic barrier.
    exact (Real.contDiffAt_log.2 hsigma_pos.ne').neg.comp 0 hsigma3
  have hneglog_second :
      iteratedDeriv 2 (fun a : ℝ ↦ -Real.log (σ a)) 0 =
        b / s + delta ^ (2 : ℕ) / s ^ (2 : ℕ) := by
    -- This is the missing scalar second-order chain rule for the normalized slack.
    exact negLog_comp_iteratedDeriv_two hsigma3 hsigma_zero hs' hsigma_deriv hsigma_second
  have hneglog_third :
      iteratedDeriv 3 (fun a : ℝ ↦ -Real.log (σ a)) 0 =
        c / s - 3 * b * delta / s ^ (2 : ℕ) - 2 * delta ^ (3 : ℕ) / s ^ (3 : ℕ) := by
    -- This is the missing scalar third-order chain rule for the normalized slack.
    exact
      negLog_comp_iteratedDeriv_three
        hsigma3
        hsigma_zero
        hs'
        hsigma_deriv
        hsigma_second
        hsigma_third
  have hlin3 : ContDiffAt ℝ 3 (fun a : ℝ ↦ a * τ) 0 := by
    -- The explicit affine correction is polynomial, hence `C³`.
    simpa [smul_eq_mul] using
      (contDiffAt_id.smul contDiffAt_const : ContDiffAt ℝ 3 (fun a : ℝ ↦ a • τ) 0)
  have hlin_second : iteratedDeriv 2 (fun a : ℝ ↦ a * τ) 0 = 0 := by
    -- A linear scalar function has vanishing second iterated derivative.
    calc
      iteratedDeriv 2 (fun a : ℝ ↦ a * τ) 0 = iteratedDeriv 2 (fun a : ℝ ↦ a) 0 * τ := by
        simpa using
          (iteratedDeriv_mul_const_field (f := fun a : ℝ ↦ a) (c := τ) (n := 2) (x := 0))
      _ = 0 := by
            simp [iteratedDeriv_fun_id]
  have hlin_third : iteratedDeriv 3 (fun a : ℝ ↦ a * τ) 0 = 0 := by
    -- The same vanishing holds at third order.
    calc
      iteratedDeriv 3 (fun a : ℝ ↦ a * τ) 0 = iteratedDeriv 3 (fun a : ℝ ↦ a) 0 * τ := by
        simpa using
          (iteratedDeriv_mul_const_field (f := fun a : ℝ ↦ a) (c := τ) (n := 3) (x := 0))
      _ = 0 := by
            simp [iteratedDeriv_fun_id]
  have hbase_slice_second :
      iteratedDeriv 2 (fun a : ℝ ↦ ψ a + a * τ) 0 = b := by
    -- Adding the explicit affine correction back restores the base slice at second order.
    calc
      iteratedDeriv 2 (fun a : ℝ ↦ ψ a + a * τ) 0
          = iteratedDeriv 2 ψ 0 + iteratedDeriv 2 (fun a : ℝ ↦ a * τ) 0 := by
              simpa using
                (iteratedDeriv_add
                  (hpsi3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
                  (hlin3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) :
                    iteratedDeriv 2 (fun a : ℝ ↦ ψ a + a * τ) 0 =
                      iteratedDeriv 2 ψ 0 + iteratedDeriv 2 (fun a : ℝ ↦ a * τ) 0)
      _ = b := by
            rw [hpsi_second, hlin_second]
            ring
  have hbase_slice_third :
      iteratedDeriv 3 (fun a : ℝ ↦ ψ a + a * τ) 0 = c := by
    -- The third derivative is likewise unchanged by the affine correction.
    calc
      iteratedDeriv 3 (fun a : ℝ ↦ ψ a + a * τ) 0
          = iteratedDeriv 3 ψ 0 + iteratedDeriv 3 (fun a : ℝ ↦ a * τ) 0 := by
              simpa using
                (iteratedDeriv_add hpsi3 hlin3 :
                    iteratedDeriv 3 (fun a : ℝ ↦ ψ a + a * τ) 0 =
                      iteratedDeriv 3 ψ 0 + iteratedDeriv 3 (fun a : ℝ ↦ a * τ) 0)
      _ = c := by
            rw [hpsi_third, hlin_third]
            ring
  have hepigraph_slice :
      directionalSlice (epigraphLogBarrier f) (x, t) (hdir, τ) =
        fun a : ℝ ↦ ψ a + a * τ - Real.log (σ a) := by
    -- Route correction: use the normalized slack slice `σ = t - ψ` so the chain-rule signs
    -- match the source proof exactly.
    simpa [ψ, σ] using
      epigraphLogBarrier_directionalSlice_eq_slack_form (f := f) x hdir t τ
  have hepigraph_contDiffAt_three : ContDiffAt ℝ 3 (epigraphLogBarrier f) (x, t) := by
    have hf3 : ContDiffAt ℝ 3 f x := h.contDiffOn.contDiffAt (h.isOpen_domain.mem_nhds hp_raw.1)
    have hbase_cont : ContDiffAt ℝ 3 (fun q : E × ℝ ↦ f q.1) (x, t) := by
      -- The base term is the pullback of `f` along the first projection.
      have hfst3 : ContDiffAt ℝ 3 (fun q : E × ℝ ↦ q.1) (x, t) := by
        simpa using (ContinuousLinearMap.fst ℝ E ℝ).contDiff.contDiffAt
      simpa using hf3.comp (x, t) hfst3
    have hslack_cont :
        ContDiffAt ℝ 3
          (sublevelLogBarrier (fun q : E × ℝ ↦ f q.1 - q.2) 0)
          (x, t) := by
      -- The logarithmic slack term is `C³` because the strict slack stays positive at `p`.
      simpa using raw_slackBarrier_contDiffAt_three h hp
    have hepigraph_eq :
        epigraphLogBarrier f =
          fun q : E × ℝ ↦
            f q.1 + sublevelLogBarrier (fun r : E × ℝ ↦ f r.1 - r.2) 0 q := by
      funext q
      simp [epigraphLogBarrier, sublevelLogBarrier, sub_eq_add_neg]
    -- Add the base pullback and the logarithmic slack term.
    simpa [hepigraph_eq] using hbase_cont.add hslack_cont
  have hsecond_formula :
      secondDirectionalDerivative (epigraphLogBarrier f) (x, t) (hdir, τ) =
        b + b / s + delta ^ (2 : ℕ) / s ^ (2 : ℕ) := by
    -- The epigraph second derivative is the sum of the base slice and the scalar `-log` slice.
    calc
      secondDirectionalDerivative (epigraphLogBarrier f) (x, t) (hdir, τ)
          = iteratedDeriv 2 (directionalSlice (epigraphLogBarrier f) (x, t) (hdir, τ)) 0 := by
              simp [secondDirectionalDerivative]
      _ = iteratedDeriv 2 (fun a : ℝ ↦ ψ a + a * τ - Real.log (σ a)) 0 := by
            rw [hepigraph_slice]
      _ = iteratedDeriv 2 (fun a : ℝ ↦ ψ a + a * τ) 0 +
            iteratedDeriv 2 (fun a : ℝ ↦ -Real.log (σ a)) 0 := by
              simpa [sub_eq_add_neg] using
                (iteratedDeriv_add
                  ((hpsi3.add hlin3).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
                  (hneglog3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) :
                    iteratedDeriv 2
                      ((fun a : ℝ ↦ ψ a + a * τ) + fun a : ℝ ↦ -Real.log (σ a)) 0 =
                        iteratedDeriv 2 (fun a : ℝ ↦ ψ a + a * τ) 0 +
                          iteratedDeriv 2 (fun a : ℝ ↦ -Real.log (σ a)) 0)
      _ = b + (b / s + delta ^ (2 : ℕ) / s ^ (2 : ℕ)) := by
            rw [hbase_slice_second, hneglog_second]
      _ = b + b / s + delta ^ (2 : ℕ) / s ^ (2 : ℕ) := by
            ring
  have hthird_formula :
      thirdDirectionalDerivative (epigraphLogBarrier f) (x, t) (hdir, τ) =
        (1 + 1 / s) * c - 3 * b * delta / s ^ (2 : ℕ) -
          2 * delta ^ (3 : ℕ) / s ^ (3 : ℕ) := by
    -- The third derivative is the corresponding sum of the base slice and the scalar `-log`
    -- slice.
    calc
      thirdDirectionalDerivative (epigraphLogBarrier f) (x, t) (hdir, τ)
          = iteratedDeriv 3 (directionalSlice (epigraphLogBarrier f) (x, t) (hdir, τ)) 0 := by
              simp [thirdDirectionalDerivative]
      _ = iteratedDeriv 3 (fun a : ℝ ↦ ψ a + a * τ - Real.log (σ a)) 0 := by
            rw [hepigraph_slice]
      _ = iteratedDeriv 3 (fun a : ℝ ↦ ψ a + a * τ) 0 +
            iteratedDeriv 3 (fun a : ℝ ↦ -Real.log (σ a)) 0 := by
              simpa [sub_eq_add_neg] using
                (iteratedDeriv_add
                  (hpsi3.add hlin3)
                  hneglog3 :
                    iteratedDeriv 3
                      ((fun a : ℝ ↦ ψ a + a * τ) + fun a : ℝ ↦ -Real.log (σ a)) 0 =
                        iteratedDeriv 3 (fun a : ℝ ↦ ψ a + a * τ) 0 +
                          iteratedDeriv 3 (fun a : ℝ ↦ -Real.log (σ a)) 0)
      _ = c + (c / s - 3 * b * delta / s ^ (2 : ℕ) -
            2 * delta ^ (3 : ℕ) / s ^ (3 : ℕ)) := by
            rw [hbase_slice_third, hneglog_third]
      _ = (1 + 1 / s) * c - 3 * b * delta / s ^ (2 : ℕ) -
            2 * delta ^ (3 : ℕ) / s ^ (3 : ℕ) := by
            ring
  have hscalar :
      |(1 + 1 / s) * c - 3 * b * delta / s ^ (2 : ℕ) -
          2 * delta ^ (3 : ℕ) / s ^ (3 : ℕ)| ≤
        2 * (Real.sqrt (b + b / s + delta ^ (2 : ℕ) / s ^ (2 : ℕ))) ^ (3 : ℕ) := by
    have hs_ne : s ≠ 0 := hs'.ne'
    have hmerge :
        |(1 + 1 / s) * c - 3 * (1 / s) * b * (delta / s) - 2 * (delta / s) ^ (3 : ℕ)| ≤
          2 * (Real.sqrt (b + (1 / s) * b + (delta / s) ^ (2 : ℕ))) ^ (3 : ℕ) := by
      -- Normalize by `λ = 1 / s` and `q = delta / s`, then apply the scalar merge lemma.
      exact
        epigraph_scalar_cubic_merge
          (b := b)
          (c := c)
          (lam := 1 / s)
          (q := delta / s)
          hbase_data.1
          (one_div_nonneg.mpr hs'.le)
          hbase_data.2
    simpa [div_eq_mul_inv, pow_two, pow_three, hs_ne, mul_assoc, mul_left_comm, mul_comm] using
      hmerge
  simpa [one_mul] using
    epigraph_third_deriv_bound_of_normalized_data
      (x := x)
      (hdir := hdir)
      (t := t)
      (τ := τ)
      (second := b + b / s + delta ^ (2 : ℕ) / s ^ (2 : ℕ))
      (third := (1 + 1 / s) * c - 3 * b * delta / s ^ (2 : ℕ) -
        2 * delta ^ (3 : ℕ) / s ^ (3 : ℕ))
      hepigraph_contDiffAt_three
      hsecond_formula
      hthird_formula
      hscalar

-- Proof sketch: repeat the self-concordance part of Theorem 5.3.5 on the canonical `L²`
-- product owner `Z = WithLp 2 (E × ℝ)`, using the canonical raw-pair bridge `ofZ`. View
-- `z ↦ f (ofZ z).1` as the affine pullback of `f` along the first projection, and view
-- `z ↦ -log ((ofZ z).2 - f (ofZ z).1)` as the logarithmic barrier term for the strict epigraph
-- inequality. The affine-precomposition theorem, the logarithmic-barrier theorem, and the sum
-- theorem yield standard self-concordance on the pulled-back strict epigraph domain, and this
-- argument does not use the barrier-parameter inequality for `f`.
/-- Helper for Corollary 5.3.1: on raw pairs `(x, t)`, the epigraph logarithmic barrier is
standard self-concordant on the strict epigraph domain, provided the base function is standard
self-concordant on `dom`. -/
private theorem raw_epigraphLogBarrier_isStandardSelfConcordantOn
    {dom : Set E} {f : E → ℝ}
    (h : IsStandardSelfConcordantOn dom f) :
    IsStandardSelfConcordantOn
      (strictConstrainedEpigraph dom f)
      (epigraphLogBarrier f) := by
  let strip : Set (E × ℝ) := {p : E × ℝ | p.1 ∈ dom}
  let gap : E × ℝ → ℝ := fun p ↦ f p.1 - p.2
  let Fbase : E × ℝ → ℝ := fun p ↦ f p.1
  let Fslack : E × ℝ → ℝ := sublevelLogBarrier gap 0
  let fstAffine : E × ℝ →ᴬ[ℝ] E := (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap
  have hbase_std : IsStandardSelfConcordantOn strip Fbase := by
    -- Pull the base owner back to raw pairs through the first projection.
    simpa [strip, Fbase, fstAffine, Function.comp] using h.comp_continuousAffineMap fstAffine
  have hbase_contDiffOn :
      ContDiffOn ℝ 3 Fbase (strictConstrainedEpigraph dom f) := by
    intro p hp
    have hp_strip : p ∈ strip := by
      simpa [strip, strictConstrainedEpigraph] using hp.1
    -- Restrict the base `C³` owner from the strip to the smaller strict epigraph.
    exact
      (hbase_std.contDiffOn.contDiffAt (hbase_std.isOpen_domain.mem_nhds hp_strip)).contDiffWithinAt
  have hslack_contDiffOn :
      ContDiffOn ℝ 3 Fslack (strictConstrainedEpigraph dom f) := by
    intro p hp
    -- The slack stays positive on the strict epigraph, so the logarithmic term is `C³` there.
    simpa [Fslack, gap] using raw_slackBarrier_contDiffAt_three h hp |>.contDiffWithinAt
  have hbase_convexOn :
      ConvexOn ℝ (strictConstrainedEpigraph dom f) Fbase := by
    refine ⟨strictConstrainedEpigraph_isConvex h, ?_⟩
    intro x hx y hy a b ha hb hab
    have hx_strip : x ∈ strip := by
      simpa [strip, strictConstrainedEpigraph] using hx.1
    have hy_strip : y ∈ strip := by
      simpa [strip, strictConstrainedEpigraph] using hy.1
    -- Restrict the base convexity owner from the strip to the strict epigraph.
    simpa [Fbase] using hbase_std.convexOn.2 hx_strip hy_strip ha hb hab
  have hslack_hessian_nonneg :
      ∀ p ∈ strictConstrainedEpigraph dom f, ∀ u : E × ℝ, 0 ≤ inner ℝ u (hessian Fslack p u) := by
    intro p hp u
    have hp_strip : p ∈ strip := by
      simpa [strip, strictConstrainedEpigraph] using hp.1
    have hp_gap : gap p < 0 := by
      simpa [gap, sub_lt_zero] using hp.2
    have hquad_ge_sq :
        (inner ℝ (∇ Fslack p) u) ^ (2 : ℕ) ≤ inner ℝ u (hessian Fslack p u) := by
      -- The strict-sublevel logarithmic barrier dominates the squared gradient pairing.
      simpa [Fslack] using
        (IsSelfConcordantOnWith.sublevelLogBarrier_hessian_quadraticForm_ge_gradient_sq
          (hself := raw_gap_isStandardSelfConcordantOn h)
          (β := 0)
          (x := p)
          (h := u)
          hp_strip
          hp_gap)
    -- The gradient-square lower bound immediately implies Hessian nonnegativity.
    nlinarith
  have hslack_convexOn :
      ConvexOn ℝ (strictConstrainedEpigraph dom f) Fslack := by
    exact
      (convexOn_iff_hessian_quadratic_form_nonneg
        (strictConstrainedEpigraph_isOpen h)
        (strictConstrainedEpigraph_isConvex h)
        (hslack_contDiffOn.of_le (by norm_num))).2
        (fun p hp u ↦ by simpa [real_inner_comm] using hslack_hessian_nonneg p hp u)
  have hsum_eq : Fbase + Fslack = epigraphLogBarrier f := by
    -- The epigraph barrier is the sum of the base pullback and the slack logarithm.
    funext p
    simp [Fbase, Fslack, gap, epigraphLogBarrier]
  refine
    { isOpen_domain := strictConstrainedEpigraph_isOpen h
      contDiffOn := by
        -- Add the base `C³` owner and the slack `C³` owner on the strict epigraph.
        simpa [hsum_eq] using hbase_contDiffOn.add hslack_contDiffOn
      convexOn := by
        -- Convexity is the sum of the restricted base convexity and the slack convexity.
        simpa [hsum_eq] using hbase_convexOn.add hslack_convexOn
      third_deriv_bound := by
        intro p hp u
        -- The only remaining blocker is the source-faithful cubic estimate on the normalized
        -- slack slice.
        simpa [one_mul] using raw_epigraphLogBarrier_third_deriv_bound h hp u }

/-- Corollary 5.3.1: if `f` is a standard self-concordant function on `dom`, then the epigraph
barrier, viewed on the canonical `L²` product owner `WithLp 2 (E × ℝ)` through `ofZ`, is also
standard self-concordant on the strict epigraph domain from Theorem 5.3.5. -/
theorem epigraphLogBarrier_isStandardSelfConcordantOn
    {dom : Set E} {f : E → ℝ}
    (h : IsStandardSelfConcordantOn dom f) :
    IsStandardSelfConcordantOn
      (ofZ ⁻¹' strictConstrainedEpigraph dom f)
      (epigraphLogBarrier f ∘ ofZ) := by
  let ofPairContinuousAffine : Z →ᴬ[ℝ] E × ℝ :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).toContinuousLinearMap).toContinuousAffineMap
  -- Route correction: the previous one-line proof tried to reuse a private barrier theorem from
  -- Theorem 5.3.5, but that theorem has the stronger barrier hypothesis and is not available as a
  -- stable public dependency. The proof now closes the raw-pair standard-self-concordance theorem
  -- locally, then transports it to the canonical `WithLp` owner through `ofZ`.
  simpa [ofPairContinuousAffine, Function.comp] using
    (raw_epigraphLogBarrier_isStandardSelfConcordantOn
      (E := E)
      (dom := dom)
      (f := f)
      h).comp_continuousAffineMap ofPairContinuousAffine

end
