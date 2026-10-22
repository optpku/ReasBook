/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Analysis.InnerProductSpace.ProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Set Topology
open scoped Gradient HessianLocalNorm

variable {E : Type u}

/- Theorem 5.3.5 lies in the Chapter 5 self-concordant-barrier / epigraph-lifting domain.

Sampled owner declarations in this domain:
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for barrier data;
* `sublevelLogBarrier` and `sublevelLogBarrier_isSelfConcordantOnWith` from `Theorem_5_1_4`, the
  canonical strict-sublevel logarithmic-barrier owner and theorem;
* `constrainedEpigraph` from `Chap03/Definition_3_3`, the chapter owner for the closed epigraph,
  whose naming pattern determines the strict epigraph owner in this file;
* mathlib `WithLp 2 (E × ℝ)` together with `WithLp.ofLp`, which supplies the canonical `L²`
  product owner and its bridge back to raw pairs;
* `selfConcordantBarrier_add_linear_isStandardSelfConcordantOn` from `Theorem_5_3_1`, the
  canonical self-concordance theorem for adding a linear term.

Source/core/bridge triage:
* source-facing: the textbook strict epigraph domain on raw pairs and the barrier
  `(x, t) ↦ f x - log (t - f x)`;
* core/canonical: `IsSelfConcordantBarrierOnWith` on the canonical `L²` product owner
  `WithLp 2 (E × ℝ)`;
* bridge/view: the raw-pair formulas transported to that owner through `WithLp.ofLp`.

Primitive data:
* the base domain `dom`;
* the base barrier `f`;
* the barrier parameter `ν`;
* the owner witness `h : IsSelfConcordantBarrierOnWith dom ν f`.

Derived API:
* the source-facing raw-pair strict epigraph `strictConstrainedEpigraph dom f`;
* the source-facing raw-pair barrier `epigraphLogBarrier f`.

This file keeps the strict epigraph domain and barrier as source-facing raw-pair data, but the
main numbered theorem lives on the canonical `L²` product owner `WithLp 2 (E × ℝ)`, so the
barrier statement uses the textbook formulas only through the raw-pair bridge `WithLp.ofLp`. -/

/-- The strict epigraph `{(x, t) | x ∈ dom ∧ f x < t}` on raw pairs. -/
def strictConstrainedEpigraph (dom : Set E) (f : E → ℝ) : Set (E × ℝ) :=
  {p | p.1 ∈ dom ∧ f p.1 < p.2}

/-- Membership in `strictConstrainedEpigraph dom f` is the textbook strict epigraph condition. -/
@[simp] theorem mem_strictConstrainedEpigraph_iff
    {dom : Set E} {f : E → ℝ} {p : E × ℝ} :
    p ∈ strictConstrainedEpigraph dom f ↔ p.1 ∈ dom ∧ f p.1 < p.2 :=
  Iff.rfl

/-- The textbook epigraph barrier on raw pairs `(x, t) ↦ f x - log (t - f x)`, implemented as
the sum of the base term `x ↦ f x` and the canonical strict-sublevel barrier for the epigraph
gap `f x - t`. -/
def epigraphLogBarrier (f : E → ℝ) : E × ℝ → ℝ :=
  fun p ↦ f p.1 + sublevelLogBarrier (fun q : E × ℝ ↦ f q.1 - q.2) 0 p

/-- Evaluating `epigraphLogBarrier f` recovers the textbook raw-pair formula. -/
@[simp] theorem epigraphLogBarrier_apply (f : E → ℝ) (p : E × ℝ) :
    epigraphLogBarrier f p = f p.1 - Real.log (p.2 - f p.1) :=
  by
    simp [epigraphLogBarrier, sublevelLogBarrier, sub_eq_add_neg, add_comm]

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable local instance instSeminormedAddCommGroupRealProdTheorem535 :
    SeminormedAddCommGroup (E × ℝ) :=
  WithLp.seminormedAddCommGroupToProd 2 E ℝ

noncomputable local instance instNormedAddCommGroupRealProdTheorem535 :
    NormedAddCommGroup (E × ℝ) :=
  WithLp.normedAddCommGroupToProd 2 E ℝ

noncomputable local instance instNormedSpaceRealProdTheorem535 :
    NormedSpace ℝ (E × ℝ) :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 E ℝ

noncomputable local instance instInnerProductSpaceRealProdTheorem535 :
    InnerProductSpace ℝ (E × ℝ) where
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
    simpa using inner_add_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) (WithLp.toLp 2 z)
  smul_left x y r := by
    change inner ℝ (r • WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      r * inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_smul_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) r

noncomputable local instance instCompleteSpaceRealProdTheorem535 :
    CompleteSpace (E × ℝ) := inferInstance

local notation "Z" => WithLp 2 (E × ℝ)
local notation "ofZ" => (WithLp.ofLp : Z → E × ℝ)

/-- Helper for Theorem 5.3.5: the canonical raw-pair bridge from the `WithLp` owner `Z` back to
`E × ℝ`, packaged as a continuous affine map so the Chapter 5 affine-pullback API can be reused
without restating the raw-pair formulas. -/
private def ofPairContinuousAffine : Z →ᴬ[ℝ] E × ℝ :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).toContinuousLinearMap).toContinuousAffineMap

omit [CompleteSpace E] in
/-- Helper for Theorem 5.3.5: applying the raw-pair affine bridge just recovers `WithLp.ofLp`. -/
@[simp] private theorem ofPairContinuousAffine_apply (z : Z) :
    ofPairContinuousAffine z = ofZ z :=
  rfl

/-- Helper for Theorem 5.3.5: on `ℝ`, the real inner product is ordinary multiplication. -/
@[simp] private theorem real_inner_eq_mul (s t : ℝ) :
    inner ℝ s t = s * t := by
  calc
    inner ℝ s t = inner ℝ (s • (1 : ℝ)) t := by simp
    _ = s * inner ℝ (1 : ℝ) t := by rw [real_inner_smul_left]
    _ = s * t := by
          congr 1
          calc
            inner ℝ (1 : ℝ) t = inner ℝ (1 : ℝ) (t • (1 : ℝ)) := by simp
            _ = t * inner ℝ (1 : ℝ) (1 : ℝ) := by rw [inner_smul_right]
            _ = t := by simp

omit [CompleteSpace E] in
/-- Helper for Theorem 5.3.5: the raw `L²` inner product on pairs splits into the first-coordinate
inner product and the scalar product of the second coordinates. -/
@[simp] private theorem inner_pair_eq
    (x y : E) (s t : ℝ) :
    inner ℝ (x, s) (y, t) = inner ℝ x y + s * t := by
  change inner ℝ (WithLp.toLp 2 (x, s)) (WithLp.toLp 2 (y, t)) = inner ℝ x y + s * t
  simp [real_inner_eq_mul]

omit [CompleteSpace E] in
/-- Helper for Theorem 5.3.5: the raw linear term in the gap owner is exactly the second
coordinate negation. -/
@[simp] private theorem raw_gap_linear_term_normalization
    (p : E × ℝ) :
    inner ℝ ((0 : E), (-1 : ℝ)) p = -p.2 := by
  -- Expand the pair inner product and simplify the scalar coordinate.
  simpa using inner_pair_eq (x := (0 : E)) (y := p.1) (s := (-1 : ℝ)) (t := p.2)

/-- Helper for Theorem 5.3.5: a `C²` real-valued map has differentiable gradient at the same
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

/-- Helper for Theorem 5.3.5: barrier structure is preserved under continuous affine pullback.
This is the direct Chapter 5 pullback argument written in the barrier-inequality form, so it does
not depend on the square-formulation file that currently fails elsewhere in the repo. -/
private theorem barrier_comp_continuousAffineMap
    {E₁ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
    {dom : Set E₁} {ν : NNReal} {F : E₁ → ℝ}
    (h : IsSelfConcordantBarrierOnWith dom ν F) (g : E →ᴬ[ℝ] E₁) :
    IsSelfConcordantBarrierOnWith (g ⁻¹' dom) ν (F ∘ g) := by
  let hstd : IsStandardSelfConcordantOn dom F := h.toIsStandardSelfConcordantOn
  refine
    { toIsStandardSelfConcordantOn := hstd.comp_continuousAffineMap g
      barrier_parameter_bound := ?_ }
  intro x hx u
  have hx_dom : g x ∈ dom := hx
  have hcont :
      ContDiffAt ℝ 2 F (g x) := by
    exact (hstd.contDiffOn.of_le (by norm_num)).contDiffAt (hstd.isOpen_domain.mem_nhds hx_dom)
  have hdiff : DifferentiableAt ℝ F (g x) := hcont.differentiableAt (by norm_num)
  have hdiff_comp : DifferentiableAt ℝ (F ∘ g) x :=
    (hcont.comp x g.contDiff.contDiffAt).differentiableAt (by norm_num)
  -- Rewrite the pullback gradient pairing and Hessian quadratic form through the affine map.
  calc
    2 * inner ℝ (∇ (F ∘ g) x) u - inner ℝ u (hessian (F ∘ g) x u)
        = 2 * inner ℝ (∇ F (g x)) (g.contLinear u) -
            inner ℝ (g.contLinear u) (hessian F (g x) (g.contLinear u)) := by
          have hgrad_eq :
              inner ℝ (∇ (F ∘ g) x) u =
                inner ℝ (∇ F (g x)) (g.contLinear u) := by
            calc
              inner ℝ (∇ (F ∘ g) x) u = fderiv ℝ (F ∘ g) x u := by
                rw [inner_gradient_left hdiff_comp]
              _ = fderiv ℝ F (g x) (g.contLinear u) := by
                simpa using
                  congrArg (fun A : E →L[ℝ] ℝ ↦ A u) (fderiv_comp x hdiff g.differentiableAt)
              _ = inner ℝ (∇ F (g x)) (g.contLinear u) := by
                rw [← inner_gradient_left hdiff]
          rw [hgrad_eq, hessianQuadraticForm_comp_affine F g x u hcont]
    _ ≤ (ν : ℝ) := h.barrier_parameter_bound hx_dom (g.contLinear u)

/-- Helper for Theorem 5.3.5: if the first coordinate carries the original `ν`-barrier, then the
raw-pair pullback `(x, t) ↦ f x` carries the same barrier structure on the strip `x ∈ dom`. -/
private theorem raw_firstCoordinate_isSelfConcordantBarrierOnWith
    {dom : Set E} {ν : NNReal} {f : E → ℝ}
    (h : IsSelfConcordantBarrierOnWith dom ν f) :
    IsSelfConcordantBarrierOnWith
      {p : E × ℝ | p.1 ∈ dom}
      ν
      (fun p : E × ℝ ↦ f p.1) := by
  let fstAffine : E × ℝ →ᴬ[ℝ] E := (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap
  -- Pull the original barrier back along the first projection on raw pairs.
  simpa [fstAffine, Function.comp] using barrier_comp_continuousAffineMap h fstAffine

/-- Helper for Theorem 5.3.5: the raw epigraph gap `(x, t) ↦ f x - t` is standard
self-concordant on the strip `x ∈ dom`, because it is the lifted base function plus the linear
term `(x, t) ↦ -t`. -/
private theorem raw_gap_isStandardSelfConcordantOn
    {dom : Set E} {f : E → ℝ}
    (h : IsStandardSelfConcordantOn dom f) :
    IsStandardSelfConcordantOn
      {p : E × ℝ | p.1 ∈ dom}
      (fun p : E × ℝ ↦ f p.1 - p.2) := by
  let fstAffine : E × ℝ →ᴬ[ℝ] E := (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap
  have hpull :
      IsStandardSelfConcordantOn
        {p : E × ℝ | p.1 ∈ dom}
        (fun p : E × ℝ ↦ f p.1) := by
    -- Pull the base self-concordant owner back to the raw-pair strip via the first projection.
    simpa [fstAffine, Function.comp] using h.comp_continuousAffineMap fstAffine
  -- Add the linear term `(x, t) ↦ -t` using the Chapter 5 linear-perturbation theorem.
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    selfConcordantBarrier_add_linear_isStandardSelfConcordantOn
      {p : E × ℝ | p.1 ∈ dom}
      (fun p : E × ℝ ↦ f p.1)
      ((0 : E), (-1 : ℝ))
      hpull

/-- Helper for Theorem 5.3.5: the raw strict epigraph is open once the gap map is continuous on
the open strip `x ∈ dom`. This isolates the source-facing domain geometry from the later
directional-derivative argument. -/
private theorem strictConstrainedEpigraph_isOpen
    {dom : Set E} {f : E → ℝ}
    (h : IsStandardSelfConcordantOn dom f) :
    IsOpen (strictConstrainedEpigraph dom f : Set (E × ℝ)) := by
  let strip : Set (E × ℝ) := {p : E × ℝ | p.1 ∈ dom}
  let gap : E × ℝ → ℝ := fun p ↦ f p.1 - p.2
  have hgap : IsStandardSelfConcordantOn strip gap := raw_gap_isStandardSelfConcordantOn h
  have hopen : IsOpen (strip ∩ gap ⁻¹' Set.Iio (0 : ℝ)) := by
    exact hgap.contDiffOn.continuousOn.isOpen_inter_preimage hgap.isOpen_domain isOpen_Iio
  -- The strict epigraph is the open strip intersected with the open sublevel of the continuous
  -- raw gap.
  convert hopen using 1
  ext p
  simp [strictConstrainedEpigraph, strip, gap]

/-- Helper for Theorem 5.3.5: the raw strict epigraph is convex because it is the strict sublevel
set `{gap < 0}` of the convex gap map `gap(x, t) = f x - t` over the convex strip `x ∈ dom`. -/
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
    simp [strictConstrainedEpigraph, strip, gap]
  rw [hrepr]
  -- Convexity follows from the convex raw-gap owner on the strip.
  exact (raw_gap_isStandardSelfConcordantOn h).convexOn.convex_lt 0

/-- Helper for Theorem 5.3.5: the slack logarithmic term `p ↦ -log (p.2 - f p.1)` is `C²` at
every raw strict-epigraph point. The proof keeps the source slack `p.2 - f p.1` explicit, which
is the controlled quantity in the textbook proof. -/
private theorem raw_slackBarrier_contDiffAt_two
    {dom : Set E} {f : E → ℝ} {p : E × ℝ}
    (h : IsStandardSelfConcordantOn dom f)
    (hp : p ∈ strictConstrainedEpigraph dom f) :
    ContDiffAt ℝ 2 (sublevelLogBarrier (fun q : E × ℝ ↦ f q.1 - q.2) 0) p := by
  let gap : E × ℝ → ℝ := fun q ↦ f q.1 - q.2
  have hp_strip : p ∈ {q : E × ℝ | q.1 ∈ dom} := by
    simpa [strictConstrainedEpigraph] using hp.1
  have hgap_cont :
      ContDiffAt ℝ 2 gap p := by
    let hgap : IsStandardSelfConcordantOn {q : E × ℝ | q.1 ∈ dom} gap :=
      raw_gap_isStandardSelfConcordantOn h
    -- Restrict the raw-gap `C³` owner to the point `p`.
    exact
      ((hgap.contDiffOn.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ (3 : WithTop ℕ∞))).contDiffAt
        (hgap.isOpen_domain.mem_nhds hp_strip))
  have hslack_pos : 0 < p.2 - f p.1 := sub_pos.mpr hp.2
  have hslack_cont :
      ContDiffAt ℝ 2 (fun q : E × ℝ ↦ q.2 - f q.1) p := by
    -- The slack is the negative raw gap, so it inherits the same regularity.
    simpa [gap, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hgap_cont.neg
  have hlog_cont :
      ContDiffAt ℝ 2 (fun q : E × ℝ ↦ Real.log (q.2 - f q.1)) p := by
    -- Compose the `C²` slack with `log` away from the singularity at zero.
    exact (Real.contDiffAt_log.2 hslack_pos.ne').comp p hslack_cont
  -- Negating the logarithm recovers the standard sublevel barrier formula.
  convert hlog_cont.neg using 1
  ext q
  simp [sublevelLogBarrier, sub_eq_add_neg, add_comm]

/-- Helper for Theorem 5.3.5: the same slack logarithmic term is in fact `C³` at every raw
strict-epigraph point. This is the regularity level needed by the standard self-concordance
owner, and the proof follows the same explicit-slack route as the `C²` helper. -/
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
    -- Restrict the raw-gap `C³` owner to the point `p`.
    exact (hgap.contDiffOn.contDiffAt (hgap.isOpen_domain.mem_nhds hp_strip))
  have hslack_pos : 0 < p.2 - f p.1 := sub_pos.mpr hp.2
  have hslack_cont :
      ContDiffAt ℝ 3 (fun q : E × ℝ ↦ q.2 - f q.1) p := by
    -- The slack is the negative raw gap, so it inherits the same regularity.
    simpa [gap, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hgap_cont.neg
  have hlog_cont :
      ContDiffAt ℝ 3 (fun q : E × ℝ ↦ Real.log (q.2 - f q.1)) p := by
    -- Compose the `C³` slack with `log` away from the singularity at zero.
    exact (Real.contDiffAt_log.2 hslack_pos.ne').comp p hslack_cont
  -- Negating the logarithm recovers the standard sublevel barrier formula.
  convert hlog_cont.neg using 1
  ext q
  simp [sublevelLogBarrier, sub_eq_add_neg, add_comm]

omit [CompleteSpace E] in
/-- Helper for Theorem 5.3.5: along a raw line `(x,t) + a • (h,τ)`, the epigraph barrier slice
has the normalized slack form used in the source proof. The extra affine term `a * τ` is kept
explicit because it disappears from the second and third derivatives later. -/
private theorem epigraphLogBarrier_directionalSlice_eq_slack_form
    {f : E → ℝ} (x h : E) (t τ : ℝ) :
    directionalSlice (epigraphLogBarrier f) (x, t) (h, τ) =
      fun a : ℝ ↦
        (directionalSlice f x h a - a * τ) + a * τ -
          Real.log (t - (directionalSlice f x h a - a * τ)) := by
  -- Expand the pair slice and rewrite the logarithmic slack into the normalized source form.
  funext a
  simp [directionalSlice, epigraphLogBarrier_apply, sub_eq_add_neg, add_comm, add_assoc, mul_comm]

/-- Helper for Theorem 5.3.5: subtracting the explicit affine correction `a * τ` from the
normalized slack slice shifts only the first derivative, while the second and third iterated
derivatives stay equal to the original Chapter 5 directional-derivative owners. -/
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
    simpa using (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const) :
      ContDiffAt ℝ 3 (fun a : ℝ ↦ x + a • u) 0)
  have hslice3 : ContDiffAt ℝ 3 (directionalSlice f x u) 0 := by
    -- Restrict the ambient `C³` owner of `f` to the affine line through `x` in direction `u`.
    have hfx3_line : ContDiffAt ℝ 3 f ((fun a : ℝ ↦ x + a • u) 0) := by
      simpa using hfx3
    simpa [directionalSlice] using hfx3_line.comp 0 hline3
  have hlin3 : ContDiffAt ℝ 3 (fun a : ℝ ↦ a * τ) 0 := by
    -- The affine correction is polynomial, so its higher iterated derivatives are trivial.
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
    calc
      deriv (fun a : ℝ ↦ a * τ) 0 = deriv (fun a : ℝ ↦ a) 0 * τ := by
        exact deriv_mul_const_field (u := fun a : ℝ ↦ a) (v := τ) (x := 0)
      _ = τ := by
        simp
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
        exact
          (iteratedDeriv_mul_const_field (f := fun a : ℝ ↦ a) (c := τ) (n := 2) (x := 0))
      _ = 0 := by
        simp [iteratedDeriv_fun_id]
  have hlin_third : iteratedDeriv 3 (fun a : ℝ ↦ a * τ) 0 = 0 := by
    calc
      iteratedDeriv 3 (fun a : ℝ ↦ a * τ) 0 = iteratedDeriv 3 (fun a : ℝ ↦ a) 0 * τ := by
        exact
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

/-- Helper for Theorem 5.3.5: the normalized source slice
`a ↦ directionalSlice f x u a - a * τ` is `C³` at the base point. This isolates the regularity
input needed for the later scalar `-log` calculus from the derivative-value bookkeeping. -/
private theorem normalized_slack_slice_contDiffAt_three
    {dom : Set E} {f : E → ℝ}
    (h : IsStandardSelfConcordantOn dom f) {x : E} (hx : x ∈ dom) (u : E) (τ : ℝ) :
    ContDiffAt ℝ 3 (fun a : ℝ ↦ directionalSlice f x u a - a * τ) 0 := by
  have hfx3 : ContDiffAt ℝ 3 f x := h.contDiffOn.contDiffAt (h.isOpen_domain.mem_nhds hx)
  have hline3 : ContDiffAt ℝ 3 (fun a : ℝ ↦ x + a • u) 0 := by
    simpa using (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const) :
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

/-- Helper for Theorem 5.3.5: the base self-concordance data for `f` can be rewritten in the
normalized scalar form `0 ≤ b` and `|c| ≤ 2 * (sqrt b)^3`, where
`b = secondDirectionalDerivative f x u` and `c = thirdDirectionalDerivative f x u`. -/
private theorem base_directional_data_sqrt_form
    {dom : Set E} {ν : NNReal} {f : E → ℝ}
    (h : IsSelfConcordantBarrierOnWith dom ν f) {x : E} (hx : x ∈ dom) (u : E) :
    0 ≤ secondDirectionalDerivative f x u ∧
      |thirdDirectionalDerivative f x u| ≤
        2 * (Real.sqrt (secondDirectionalDerivative f x u)) ^ (3 : ℕ) := by
  let hstd : IsStandardSelfConcordantOn dom f := h.toIsStandardSelfConcordantOn
  have hfx3 : ContDiffAt ℝ 3 f x := hstd.contDiffOn.contDiffAt (hstd.isOpen_domain.mem_nhds hx)
  have hfx2 : ContDiffAt ℝ 2 f x := hfx3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hsecond_eq :
      secondDirectionalDerivative f x u = inner ℝ u (hessian f x u) :=
    secondDirectionalDerivative_eq_hessian_quadratic_form hfx2
  have hsecond_nonneg : 0 ≤ secondDirectionalDerivative f x u := by
    -- Rewrite the second directional derivative as the Hessian quadratic form of the base
    -- barrier, then use Hessian positive semidefiniteness on the domain.
    rw [hsecond_eq]
    exact hstd.hessian_posSemidef hx u
  constructor
  · exact hsecond_nonneg
  · -- Replace the Hessian local norm by the square root of the second directional derivative.
    calc
      |thirdDirectionalDerivative f x u|
          ≤ 2 * (1 : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) := by
            simpa using hstd.third_deriv_bound hx u
      _ = 2 * (Real.sqrt (inner ℝ u (hessian f x u))) ^ (3 : ℕ) := by
            rw [hessianLocalNorm_def]
            ring
      _ = 2 * (Real.sqrt (secondDirectionalDerivative f x u)) ^ (3 : ℕ) := by
            rw [hsecond_eq]

/-- Helper for Theorem 5.3.5: once the normalized second- and third-derivative formulas for the
epigraph slice are available, the final Chapter 5 cubic estimate is just the standard rewrite of
the Hessian local norm through the second directional derivative. -/
private theorem epigraphLogBarrier_third_deriv_bound_of_normalized_data
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
  have hquad :
      inner ℝ (hdir, τ) (hessian (epigraphLogBarrier f) (x, t) (hdir, τ)) = second := by
    -- Rewrite the local quadratic form by the owner-level second directional derivative bridge.
    calc
      inner ℝ (hdir, τ) (hessian (epigraphLogBarrier f) (x, t) (hdir, τ))
          = secondDirectionalDerivative (epigraphLogBarrier f) (x, t) (hdir, τ) := by
              symm
              exact secondDirectionalDerivative_eq_hessian_quadratic_form hcont2
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

/-- Helper for Theorem 5.3.5: composing `-log` with a positive scalar slack slice gives the
expected second iterated derivative at the base point. -/
private theorem negLogCompIteratedDerivTwo
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

/-- Helper for Theorem 5.3.5: composing `-log` with a positive scalar slack slice gives the
expected third iterated derivative at the base point. -/
private theorem negLogCompIteratedDerivThree
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
      _ = (-1) ^ (2 : ℕ) * (Nat.factorial 2 : ℝ) * s ^ (-1 - (2 : ℤ)) := by
            exact iter_deriv_inv 2 s
      _ = 2 * s ^ (-3 : ℤ) := by
            norm_num
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

/-- Helper for Theorem 5.3.5: the normalized positive cubic expression is controlled by the
cube of the total square-root sum. -/
private theorem normalizedCubicPositiveBound
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
    -- The factored remainder shows the positive cubic expression is bounded by the cube term.
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

/-- Helper for Theorem 5.3.5: after normalizing the strict slack by
`λ = 1 / s` and `q = delta / s`, the epigraph cubic estimate reduces to a scalar merge
inequality. -/
private theorem epigraphScalarCubicMerge
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
      normalizedCubicPositiveBound
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

/-- Helper for Theorem 5.3.5: the raw-pair epigraph barrier should be proved standard
self-concordant on the strict epigraph by following the source slack-line route. -/
private theorem raw_epigraphLogBarrier_isStandardSelfConcordantOn
    {dom : Set E} {ν : NNReal} {f : E → ℝ}
    (h : IsSelfConcordantBarrierOnWith dom ν f) :
    IsStandardSelfConcordantOn
      (strictConstrainedEpigraph dom f)
      (epigraphLogBarrier f) := by
  -- Route correction: the apparent `sublevelLogBarrier_isSelfConcordantOnWith` shortcut fails
  -- here because the raw gap `(x, t) ↦ f x - t` has no global lower bound on the strip `x ∈ dom`.
  -- The current patch stabilizes the owner skeleton: openness, `C³` regularity, and convexity are
  -- now reduced to explicit raw-pair helpers, leaving only the cubic derivative estimate on the
  -- normalized slack slice as the remaining source-faithful blocker.
  let strip : Set (E × ℝ) := {p : E × ℝ | p.1 ∈ dom}
  let gap : E × ℝ → ℝ := fun p ↦ f p.1 - p.2
  let Fbase : E × ℝ → ℝ := fun p ↦ f p.1
  let Fslack : E × ℝ → ℝ := sublevelLogBarrier gap 0
  have hbase_owner :
      IsSelfConcordantBarrierOnWith strip ν Fbase :=
    raw_firstCoordinate_isSelfConcordantBarrierOnWith h
  have hbase_std : IsStandardSelfConcordantOn strip Fbase :=
    hbase_owner.toIsStandardSelfConcordantOn
  have hbase_contDiffOn :
      ContDiffOn ℝ 3 Fbase (strictConstrainedEpigraph dom f) := by
    intro p hp
    have hp_strip : p ∈ strip := by
      simpa [strip, strictConstrainedEpigraph] using hp.1
    -- The base pullback is `C³` on the strip, hence on the smaller strict epigraph.
    exact
      (hbase_std.contDiffOn.contDiffAt (hbase_std.isOpen_domain.mem_nhds hp_strip)).contDiffWithinAt
  have hslack_contDiffOn :
      ContDiffOn ℝ 3 Fslack (strictConstrainedEpigraph dom f) := by
    intro p hp
    -- The slack logarithm is `C³` at every strict-epigraph point because the slack stays
    -- strictly positive there.
    exact (raw_slackBarrier_contDiffAt_three h.toIsStandardSelfConcordantOn hp).contDiffWithinAt
  have hbase_convexOn :
      ConvexOn ℝ (strictConstrainedEpigraph dom f) Fbase := by
    refine ⟨strictConstrainedEpigraph_isConvex h.toIsStandardSelfConcordantOn, ?_⟩
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
      simpa [Fslack] using
        (IsSelfConcordantOnWith.sublevelLogBarrier_hessian_quadraticForm_ge_gradient_sq
          (hself := raw_gap_isStandardSelfConcordantOn h.toIsStandardSelfConcordantOn)
          (β := 0)
          (x := p)
          (h := u)
          hp_strip
          hp_gap)
    nlinarith
  have hslack_convexOn :
      ConvexOn ℝ (strictConstrainedEpigraph dom f) Fslack := by
    exact
      (convexOn_iff_hessian_quadratic_form_nonneg
        (strictConstrainedEpigraph_isOpen h.toIsStandardSelfConcordantOn)
        (strictConstrainedEpigraph_isConvex h.toIsStandardSelfConcordantOn)
        (hslack_contDiffOn.of_le (by norm_num))).2
        (fun p hp u ↦ by simpa [real_inner_comm] using hslack_hessian_nonneg p hp u)
  have hepigraph_eq :
      epigraphLogBarrier f = fun p : E × ℝ ↦ f p.1 + -Real.log (p.2 - f p.1) := by
    funext p
    simp [epigraphLogBarrier_apply, sub_eq_add_neg]
  have hsum_eq : Fbase + Fslack = epigraphLogBarrier f := by
    funext p
    simp [Fbase, Fslack, gap, sublevelLogBarrier, sub_eq_add_neg]
  refine
    { isOpen_domain := strictConstrainedEpigraph_isOpen h.toIsStandardSelfConcordantOn
      contDiffOn := by
        -- The epigraph barrier splits into the base pullback plus the slack logarithm.
        simpa [hepigraph_eq, epigraphLogBarrier, Fbase, Fslack, gap, sublevelLogBarrier] using
          hbase_contDiffOn.add hslack_contDiffOn
      convexOn := by
        -- Convexity follows by adding the restricted base convexity and the slack convexity.
        simpa [hsum_eq] using hbase_convexOn.add hslack_convexOn
      third_deriv_bound := by
        intro p hp u
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
          normalized_slack_slice_derivative_data h.toIsStandardSelfConcordantOn hp_raw.1 hdir τ
        let s : ℝ := t - f x
        let delta : ℝ := τ - inner ℝ (∇ f x) hdir
        let b : ℝ := secondDirectionalDerivative f x hdir
        let c : ℝ := thirdDirectionalDerivative f x hdir
        let ψ : ℝ → ℝ := fun a : ℝ ↦ directionalSlice f x hdir a - a * τ
        let σ : ℝ → ℝ := fun a : ℝ ↦ t - ψ a
        have hs' : 0 < s := by
          simpa [s] using hs
        have hslice_zero :
            ψ 0 = f x := by
          -- The normalized slice starts at the base value `f x`, exactly as in the source proof.
          simp [ψ, directionalSlice]
        have hslice_deriv :
            deriv ψ 0 = -delta := by
          -- The affine correction shifts only the first derivative by `-τ`.
          simpa [ψ, delta, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            hslice_data.1
        have hslice_second :
            iteratedDeriv 2 ψ 0 = b := by
          -- The second derivative is the base second directional derivative `b`.
          simpa [ψ, b] using hslice_data.2.1
        have hslice_third :
            iteratedDeriv 3 ψ 0 = c := by
          -- The third derivative is the base third directional derivative `c`.
          simpa [ψ, c] using hslice_data.2.2
        have hslice3 :
            ContDiffAt ℝ 3 ψ 0 := by
          -- The normalized source slice is already `C³` at the base point.
          simpa [ψ] using
            normalized_slack_slice_contDiffAt_three h.toIsStandardSelfConcordantOn hp_raw.1 hdir τ
        have hbase_data :
            0 ≤ b ∧ |c| ≤ 2 * (Real.sqrt b) ^ (3 : ℕ) := by
          -- Rewrite the base self-concordance inequality into the scalar `(b, c)` notation.
          simpa [b, c] using base_directional_data_sqrt_form h hp_raw.1 hdir
        have hsigma_zero : σ 0 = s := by
          -- The normalized slack starts at the geometric slack `s = t - f x`.
          simp [σ, ψ, s, directionalSlice]
        have hsigma3 : ContDiffAt ℝ 3 σ 0 := by
          -- The slack slice is the constant `t` minus the normalized source slice.
          simpa [σ] using (contDiffAt_const.sub hslice3)
        have hpsi_diff : DifferentiableAt ℝ ψ 0 :=
          hslice3.differentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
        have hsigma_deriv : deriv σ 0 = delta := by
          -- Differentiating `σ = t - ψ` flips the sign of the normalized first derivative.
          have hconst_diff : DifferentiableAt ℝ (fun a : ℝ ↦ t) 0 := by
            fun_prop
          calc
            deriv σ 0 = deriv (fun a : ℝ ↦ t) 0 - deriv ψ 0 := by
              simpa [σ] using
                (deriv_sub
                  hconst_diff
                  hpsi_diff :
                    deriv (fun a : ℝ ↦ t - ψ a) 0 =
                      deriv (fun a : ℝ ↦ t) 0 - deriv ψ 0)
            _ = delta := by
              rw [hslice_deriv]
              simp [delta]
        have hsigma_second : iteratedDeriv 2 σ 0 = -b := by
          -- From second order onward, `σ` is just the negated normalized slice.
          calc
            iteratedDeriv 2 σ 0 = iteratedDeriv 2 (fun a : ℝ ↦ t) 0 - iteratedDeriv 2 ψ 0 := by
              simpa [σ] using
                (iteratedDeriv_sub
                  (contDiffAt_const.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
                  (hslice3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) :
                    iteratedDeriv 2 (fun a : ℝ ↦ t - ψ a) 0 =
                      iteratedDeriv 2 (fun a : ℝ ↦ t) 0 - iteratedDeriv 2 ψ 0)
            _ = -b := by
              rw [hslice_second]
              simp [iteratedDeriv_const]
        have hsigma_third : iteratedDeriv 3 σ 0 = -c := by
          -- The same sign flip persists at third order.
          calc
            iteratedDeriv 3 σ 0 = iteratedDeriv 3 (fun a : ℝ ↦ t) 0 - iteratedDeriv 3 ψ 0 := by
              simpa [σ] using
                (iteratedDeriv_sub contDiffAt_const hslice3 :
                  iteratedDeriv 3 (fun a : ℝ ↦ t - ψ a) 0 =
                    iteratedDeriv 3 (fun a : ℝ ↦ t) 0 - iteratedDeriv 3 ψ 0)
            _ = -c := by
              rw [hslice_third]
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
          -- This is the scalar second-order chain rule for the normalized slack.
          exact
            negLogCompIteratedDerivTwo hsigma3 hsigma_zero hs' hsigma_deriv hsigma_second
        have hneglog_third :
            iteratedDeriv 3 (fun a : ℝ ↦ -Real.log (σ a)) 0 =
              c / s - 3 * b * delta / s ^ (2 : ℕ) - 2 * delta ^ (3 : ℕ) / s ^ (3 : ℕ) := by
          -- This is the scalar third-order chain rule for the normalized slack.
          exact
            negLogCompIteratedDerivThree
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
            iteratedDeriv 2 (fun a : ℝ ↦ a * τ) 0 =
                iteratedDeriv 2 (fun a : ℝ ↦ a) 0 * τ := by
                  exact
                    (iteratedDeriv_mul_const_field
                      (f := fun a : ℝ ↦ a)
                      (c := τ)
                      (n := 2)
                      (x := 0))
            _ = 0 := by
              simp [iteratedDeriv_fun_id]
        have hlin_third : iteratedDeriv 3 (fun a : ℝ ↦ a * τ) 0 = 0 := by
          -- The same vanishing holds at third order.
          calc
            iteratedDeriv 3 (fun a : ℝ ↦ a * τ) 0 =
                iteratedDeriv 3 (fun a : ℝ ↦ a) 0 * τ := by
                  exact
                    (iteratedDeriv_mul_const_field
                      (f := fun a : ℝ ↦ a)
                      (c := τ)
                      (n := 3)
                      (x := 0))
            _ = 0 := by
              simp [iteratedDeriv_fun_id]
        have hbase_slice_second :
            iteratedDeriv 2 (fun a : ℝ ↦ ψ a + a * τ) 0 = b := by
          -- Adding the explicit affine correction back restores the base slice at second order.
          calc
            iteratedDeriv 2 (fun a : ℝ ↦ ψ a + a * τ) 0 =
                iteratedDeriv 2 ψ 0 + iteratedDeriv 2 (fun a : ℝ ↦ a * τ) 0 := by
                  simpa using
                    (iteratedDeriv_add
                      (hslice3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
                      (hlin3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) :
                        iteratedDeriv 2 (fun a : ℝ ↦ ψ a + a * τ) 0 =
                          iteratedDeriv 2 ψ 0 + iteratedDeriv 2 (fun a : ℝ ↦ a * τ) 0)
            _ = b := by
              rw [hslice_second, hlin_second]
              ring
        have hbase_slice_third :
            iteratedDeriv 3 (fun a : ℝ ↦ ψ a + a * τ) 0 = c := by
          -- The third derivative is likewise unchanged by the affine correction.
          calc
            iteratedDeriv 3 (fun a : ℝ ↦ ψ a + a * τ) 0 =
                iteratedDeriv 3 ψ 0 + iteratedDeriv 3 (fun a : ℝ ↦ a * τ) 0 := by
                  simpa using
                    (iteratedDeriv_add hslice3 hlin3 :
                      iteratedDeriv 3 (fun a : ℝ ↦ ψ a + a * τ) 0 =
                        iteratedDeriv 3 ψ 0 + iteratedDeriv 3 (fun a : ℝ ↦ a * τ) 0)
            _ = c := by
              rw [hslice_third, hlin_third]
              ring
        have hepigraph_slice :
            directionalSlice (epigraphLogBarrier f) (x, t) (hdir, τ) =
              fun a : ℝ ↦ ψ a + a * τ - Real.log (σ a) := by
          -- This is the textbook slack-line normalization of the epigraph barrier slice.
          simpa [ψ, σ] using epigraphLogBarrier_directionalSlice_eq_slack_form (f := f) x hdir t τ
        have hepigraph_contDiffAt_three : ContDiffAt ℝ 3 (epigraphLogBarrier f) (x, t) := by
          have hp_nhds :
              strictConstrainedEpigraph dom f ∈ 𝓝 (x, t) :=
            (strictConstrainedEpigraph_isOpen h.toIsStandardSelfConcordantOn).mem_nhds hp
          have hbase_at : ContDiffAt ℝ 3 Fbase (x, t) := hbase_contDiffOn.contDiffAt hp_nhds
          have hslack_at : ContDiffAt ℝ 3 Fslack (x, t) := hslack_contDiffOn.contDiffAt hp_nhds
          -- Add the base `C³` owner and the slack `C³` owner at the current epigraph point.
          simpa [hepigraph_eq, epigraphLogBarrier, Fbase, Fslack, gap, sublevelLogBarrier] using
            hbase_at.add hslack_at
        have hsecond_formula :
            secondDirectionalDerivative (epigraphLogBarrier f) (x, t) (hdir, τ) =
              b + b / s + delta ^ (2 : ℕ) / s ^ (2 : ℕ) := by
          -- The epigraph second derivative is the sum of the base slice and the scalar `-log`
          -- slice.
          calc
            secondDirectionalDerivative (epigraphLogBarrier f) (x, t) (hdir, τ) =
                iteratedDeriv 2 (directionalSlice (epigraphLogBarrier f) (x, t) (hdir, τ)) 0 := by
                  simp [secondDirectionalDerivative]
            _ = iteratedDeriv 2 (fun a : ℝ ↦ ψ a + a * τ - Real.log (σ a)) 0 := by
              rw [hepigraph_slice]
            _ = iteratedDeriv 2 (fun a : ℝ ↦ ψ a + a * τ) 0 +
                  iteratedDeriv 2 (fun a : ℝ ↦ -Real.log (σ a)) 0 := by
                    simpa [sub_eq_add_neg] using
                      (iteratedDeriv_add
                        ((hslice3.add hlin3).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
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
          -- The third derivative is the corresponding sum of the base slice and the scalar
          -- `-log` slice.
          calc
            thirdDirectionalDerivative (epigraphLogBarrier f) (x, t) (hdir, τ) =
                iteratedDeriv 3 (directionalSlice (epigraphLogBarrier f) (x, t) (hdir, τ)) 0 := by
                  simp [thirdDirectionalDerivative]
            _ = iteratedDeriv 3 (fun a : ℝ ↦ ψ a + a * τ - Real.log (σ a)) 0 := by
              rw [hepigraph_slice]
            _ = iteratedDeriv 3 (fun a : ℝ ↦ ψ a + a * τ) 0 +
                  iteratedDeriv 3 (fun a : ℝ ↦ -Real.log (σ a)) 0 := by
                    simpa [sub_eq_add_neg] using
                      (iteratedDeriv_add
                        (hslice3.add hlin3)
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
              epigraphScalarCubicMerge
                (b := b)
                (c := c)
                (lam := 1 / s)
                (q := delta / s)
                hbase_data.1
                (one_div_nonneg.mpr hs'.le)
                hbase_data.2
          -- Re-expand the normalized variables into the exact target form.
          simpa [div_eq_mul_inv, pow_two, pow_three, hs_ne, mul_assoc, mul_left_comm, mul_comm]
            using hmerge
        simpa [one_mul] using
          epigraphLogBarrier_third_deriv_bound_of_normalized_data
            hepigraph_contDiffAt_three hsecond_formula hthird_formula hscalar }

/-- Helper for Theorem 5.3.5: once the raw standard-self-concordance part is in place, the
barrier parameter is obtained by combining the base `ν`-barrier estimate on `(x, t) ↦ f x` with
the unit logarithmic estimate for the slack term `-\log (t - f x)`. -/
private theorem raw_epigraphLogBarrier_isSelfConcordantBarrierOnWith
    {dom : Set E} {ν : NNReal} {f : E → ℝ}
    (h : IsSelfConcordantBarrierOnWith dom ν f) :
    IsSelfConcordantBarrierOnWith
      (strictConstrainedEpigraph dom f)
      (ν + 1)
      (epigraphLogBarrier f) := by
  let strip : Set (E × ℝ) := {p : E × ℝ | p.1 ∈ dom}
  let gap : E × ℝ → ℝ := fun p ↦ f p.1 - p.2
  let Fbase : E × ℝ → ℝ := fun p ↦ f p.1
  let Fslack : E × ℝ → ℝ := sublevelLogBarrier gap 0
  let hstd : IsStandardSelfConcordantOn (strictConstrainedEpigraph dom f) (epigraphLogBarrier f) :=
    raw_epigraphLogBarrier_isStandardSelfConcordantOn h
  refine
    { toIsStandardSelfConcordantOn := hstd
      barrier_parameter_bound := ?_ }
  intro p hp u
  have hp_strip : p ∈ strip := by
    simpa [strip, strictConstrainedEpigraph] using hp.1
  have hp_gap : gap p < 0 := by
    simpa [gap, sub_lt_zero] using hp.2
  have hbase_owner :
      IsSelfConcordantBarrierOnWith strip ν Fbase :=
    raw_firstCoordinate_isSelfConcordantBarrierOnWith h
  have hbase_bound :
      2 * inner ℝ (∇ Fbase p) u - inner ℝ u (hessian Fbase p u) ≤ (ν : ℝ) :=
    hbase_owner.barrier_parameter_bound hp_strip u
  have hslack_quad :
      (inner ℝ (∇ Fslack p) u) ^ (2 : ℕ) ≤
        inner ℝ u (hessian Fslack p u) := by
    -- The logarithmic slack term satisfies the unit Hessian-versus-gradient-square inequality.
    simpa [Fslack] using
      (IsSelfConcordantOnWith.sublevelLogBarrier_hessian_quadraticForm_ge_gradient_sq
        (hself := raw_gap_isStandardSelfConcordantOn h.toIsStandardSelfConcordantOn)
        (β := 0)
        (x := p)
        (h := u)
        hp_strip
        hp_gap)
  have hslack_bound :
      2 * inner ℝ (∇ Fslack p) u - inner ℝ u (hessian Fslack p u) ≤ (1 : ℝ) := by
    -- From `a^2 ≤ q`, the scalar inequality `2a - q ≤ 1` follows from `(a - 1)^2 ≥ 0`.
    have hsq : 0 ≤ (inner ℝ (∇ Fslack p) u - 1) ^ (2 : ℕ) := by
      positivity
    nlinarith
  have hFbase_c2 : ContDiffAt ℝ 2 Fbase p := by
    let hbase_std : IsStandardSelfConcordantOn strip Fbase :=
      hbase_owner.toIsStandardSelfConcordantOn
    -- The pulled-back base barrier is `C²` on the strip.
    exact
      ((hbase_std.contDiffOn.of_le (by norm_num)).contDiffAt
        (hbase_std.isOpen_domain.mem_nhds hp_strip))
  have hFslack_c2 : ContDiffAt ℝ 2 Fslack p :=
    raw_slackBarrier_contDiffAt_two h.toIsStandardSelfConcordantOn hp
  have hFbase : DifferentiableAt ℝ Fbase p := hFbase_c2.differentiableAt (by norm_num)
  have hFslack : DifferentiableAt ℝ Fslack p := hFslack_c2.differentiableAt (by norm_num)
  have hgrad_base : DifferentiableAt ℝ (∇ Fbase) p :=
    differentiableAt_gradient_of_contDiffAt_two hFbase_c2
  have hgrad_slack : DifferentiableAt ℝ (∇ Fslack) p :=
    differentiableAt_gradient_of_contDiffAt_two hFslack_c2
  have hgrad :
      ∇ (Fbase + Fslack) p = ∇ Fbase p + ∇ Fslack p := by
    rw [gradient, fderiv_add hFbase hFslack]
    simp [gradient]
  have hgrad_nhds :
      (fun y ↦ ∇ (Fbase + Fslack) y) =ᶠ[𝓝 p] fun y ↦ ∇ Fbase y + ∇ Fslack y := by
    filter_upwards
      [hbase_owner.toIsStandardSelfConcordantOn.isOpen_domain.mem_nhds hp_strip,
        (strictConstrainedEpigraph_isOpen h.toIsStandardSelfConcordantOn).mem_nhds hp] with
      y hy_strip hy_epi
    have hy_base : DifferentiableAt ℝ Fbase y := by
      let hbase_std : IsStandardSelfConcordantOn strip Fbase :=
        hbase_owner.toIsStandardSelfConcordantOn
      exact
        ((hbase_std.contDiffOn.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ (3 : WithTop ℕ∞))).contDiffAt
          (hbase_std.isOpen_domain.mem_nhds hy_strip)).differentiableAt
          (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    have hy_slack : DifferentiableAt ℝ Fslack y := by
      exact (raw_slackBarrier_contDiffAt_two h.toIsStandardSelfConcordantOn hy_epi).differentiableAt
        (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    rw [gradient, fderiv_add hy_base hy_slack]
    simp [gradient]
  have hhess : hessian (Fbase + Fslack) p = hessian Fbase p + hessian Fslack p := by
    rw [hessian, hgrad_nhds.fderiv_eq, fderiv_fun_add hgrad_base hgrad_slack]
  -- Expand the raw epigraph barrier as the base pullback plus the slack logarithm and add the
  -- two parameter bounds.
  calc
    2 * inner ℝ (∇ (epigraphLogBarrier f) p) u - inner ℝ u (hessian (epigraphLogBarrier f) p u)
        = (2 * inner ℝ (∇ Fbase p) u - inner ℝ u (hessian Fbase p u)) +
            (2 * inner ℝ (∇ Fslack p) u - inner ℝ u (hessian Fslack p u)) := by
          rw [show epigraphLogBarrier f = Fbase + Fslack by rfl, hgrad, hhess]
          simp [inner_add_left, inner_add_right, ContinuousLinearMap.add_apply, two_mul,
            sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ ≤ (ν : ℝ) + 1 := add_le_add hbase_bound hslack_bound
    _ = ((ν + 1 : NNReal) : ℝ) := by
          exact_mod_cast rfl

-- Proof sketch: regard `z ↦ f (ofZ z).1` as the pullback of the given barrier along the first
-- projection on the canonical `L²` product owner `Z = WithLp 2 (E × ℝ)`, and regard
-- `sublevelLogBarrier (fun q ↦ f q.1 - q.2) 0` as the logarithmic barrier of the strict
-- sublevel set of the epigraph gap. The pullback theorem, the logarithmic-barrier theorem, and
-- the barrier-sum theorem then give a self-concordant barrier with parameter `ν + 1` on the
-- pulled-back strict epigraph domain.
/-- Theorem 5.3.5: if `f` is a `ν`-self-concordant barrier on `dom`, then
the textbook epigraph barrier, viewed on the canonical `L²` product owner
`WithLp 2 (E × ℝ)` through `WithLp.ofLp`, is a `(\nu + 1)`-self-concordant barrier on the
strict epigraph domain. -/
theorem epigraphLogBarrier_isSelfConcordantBarrierOnWith
    {dom : Set E} {ν : NNReal} {f : E → ℝ}
    (h : IsSelfConcordantBarrierOnWith dom ν f) :
    IsSelfConcordantBarrierOnWith
      (ofZ ⁻¹' strictConstrainedEpigraph dom f)
      (ν + 1)
      (epigraphLogBarrier f ∘ ofZ) := by
  -- First prove the raw-pair barrier theorem, then transport it to the canonical `WithLp` owner.
  simpa [ofPairContinuousAffine, Function.comp] using
    barrier_comp_continuousAffineMap
      (raw_epigraphLogBarrier_isSelfConcordantBarrierOnWith h)
      ofPairContinuousAffine

end
