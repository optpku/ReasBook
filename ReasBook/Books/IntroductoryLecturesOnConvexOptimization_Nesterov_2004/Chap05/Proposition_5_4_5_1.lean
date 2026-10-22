/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.ProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_5_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_5_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open Set Topology Filter
open StrictPositiveSemidefiniteCone
open scoped BigOperators Gradient RealInnerProductSpace RealSymmetricMatrixSpace

variable {m n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n

noncomputable local instance instLocalChap05_Proposition_5_4_5_11 : SeminormedAddCommGroup (SymmMat × ℝ) :=
  WithLp.seminormedAddCommGroupToProd 2 SymmMat ℝ

noncomputable local instance instLocalChap05_Proposition_5_4_5_12 : NormedAddCommGroup (SymmMat × ℝ) :=
  WithLp.normedAddCommGroupToProd 2 SymmMat ℝ

noncomputable local instance instLocalChap05_Proposition_5_4_5_13 : NormedSpace ℝ (SymmMat × ℝ) :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 SymmMat ℝ

noncomputable local instance instInnerProductSpaceChap05_Proposition_5_4_5_11 : InnerProductSpace ℝ (SymmMat × ℝ) where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 SymmMat ℝ x]
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

noncomputable local instance instLocalChap05_Proposition_5_4_5_14 : CompleteSpace (SymmMat × ℝ) := inferInstance

section

variable (a : Fin m → E) (b : Fin m → ℝ) (v : E)

local notation "𝒟" => circumscribedEllipsoidBarrierAmbientDomain a b v
local notation "F" => circumscribedEllipsoidBarrierAmbient a b v
local notation "cτ" => ((0 : SymmMat), (1 : ℝ))
local notation "P" => circumscribedEllipsoidOptimizationProblem a b v

/-- Helper for Proposition 5.4.5.1: on `ℝ`, the real inner product is ordinary multiplication. -/
@[simp] theorem real_inner_eq_mul (s t : ℝ) :
    inner ℝ s t = s * t := by
  -- Rewrite the scalar inner product through the canonical basis vector `1 : ℝ`.
  calc
    inner ℝ s t = inner ℝ (s • (1 : ℝ)) t := by simp
    _ = s * inner ℝ (1 : ℝ) t := by rw [real_inner_smul_left]
    _ = s * t := by
          congr 1
          calc
            inner ℝ (1 : ℝ) t = inner ℝ (1 : ℝ) (t • (1 : ℝ)) := by simp
            _ = t * inner ℝ (1 : ℝ) (1 : ℝ) := by rw [inner_smul_right]
            _ = t := by simp

/-- Helper for Proposition 5.4.5.1: differentiating the linear-tilted penalty objective
`z ↦ t ⟪c, z⟫ + f z` adds the barrier gradient to the linear tilt. -/
theorem hasGradientAt_penaltyObjective
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [CompleteSpace E']
    (c : E') (f : E' → ℝ) (t : ℝ) {x : E'}
    (hf_diff : DifferentiableAt ℝ f x) :
    HasGradientAt (fun z : E' ↦ t * inner ℝ c z + f z) ((t : ℝ) • c + ∇ f x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hlinear : HasFDerivAt (fun z : E' ↦ t * inner ℝ c z) ((t : ℝ) • innerSL ℝ c) x := by
    -- The penalty tilt is linear, so its derivative is the same linear map everywhere.
    simpa using (((t : ℝ) • innerSL ℝ c).hasFDerivAt :
      HasFDerivAt (fun z : E' ↦ ((t : ℝ) • innerSL ℝ c) z) ((t : ℝ) • innerSL ℝ c) x)
  -- Differentiate the linear tilt first, then add the barrier contribution.
  simpa using hlinear.add hf_diff.hasGradientAt.hasFDerivAt

/-- Helper for Proposition 5.4.5.1: any exact minimizer of the penalty objective at parameter
`T` satisfies the stationarity equation `∇ f xBase = -(T : ℝ) • c`. -/
theorem penaltyMinimizer_gradient_eq_neg_smul
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    {dom : Set E'} {ν : NNReal} {f : E' → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν f]
    (c : E')
    (T : Set.Ici (0 : ℝ))
    {xBase : dom}
    (hbase :
      IsMinOn
        (fun z : E' ↦ (T : ℝ) * inner ℝ c z + f z)
        dom
        (xBase : E')) :
    ∇ f (xBase : E') = -((T : ℝ) • c) := by
  let hstd : IsStandardSelfConcordantOn dom f := inferInstance
  have hdiff : DifferentiableAt ℝ f (xBase : E') := by
    exact
      (hstd.contDiffOn.contDiffAt (hstd.isOpen_domain.mem_nhds xBase.2)).differentiableAt
        (by norm_num)
  have hlocal : IsLocalMin (fun z : E' ↦ (T : ℝ) * inner ℝ c z + f z) (xBase : E') :=
    hbase.isLocalMin (hstd.isOpen_domain.mem_nhds xBase.2)
  have hgrad :
      ∇ (fun z : E' ↦ (T : ℝ) * inner ℝ c z + f z) (xBase : E') =
        (T : ℝ) • c + ∇ f (xBase : E') :=
    (hasGradientAt_penaltyObjective c f (T : ℝ) hdiff).gradient
  have hzero : ∇ (fun z : E' ↦ (T : ℝ) * inner ℝ c z + f z) (xBase : E') = 0 :=
    isLocalMin_gradient_eq_zero hlocal
  -- Read the first-order optimality condition back as the barrier gradient identity.
  rw [hgrad] at hzero
  simpa [eq_neg_iff_add_eq_zero, add_comm, add_left_comm, add_assoc] using hzero

/-- Helper for Proposition 5.4.5.1: a unit-penalty minimizer rewrites the explicit penalty family
`z ↦ t ⟪c, z⟫ + f z` into the auxiliary-central-path objective based at that minimizer. -/
theorem penaltyObjective_eq_auxiliaryOfUnitMinimizer
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    {dom : Set E'} {ν : NNReal} {f : E' → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν f]
    (c : E')
    {xBase : dom}
    (hbase :
      IsMinOn
        (fun z : E' ↦ inner ℝ c z + f z)
        dom
        (xBase : E')) :
    ∀ t : ℝ,
      (fun z : E' ↦ t * inner ℝ c z + f z) = auxiliaryCentralPathObjective f xBase t := by
  have hbase' :
      IsMinOn
        (fun z : E' ↦ ((⟨1, by norm_num⟩ : Set.Ici (0 : ℝ)) : ℝ) * inner ℝ c z + f z)
        dom
        (xBase : E') := by
    simpa using hbase
  have hgrad :
      ∇ f (xBase : E') = -c := by
    simpa using
      (@penaltyMinimizer_gradient_eq_neg_smul E' _ _ _ dom ν f _
        c (⟨1, by norm_num⟩ : Set.Ici (0 : ℝ)) xBase hbase')
  intro t
  funext z
  -- Rewrite the base-point gradient so the penalty family matches the auxiliary objective.
  rw [auxiliaryCentralPathObjective_apply, hgrad]
  simpa [inner_neg_left, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Proposition 5.4.5.1: the ambient objective direction `cτ` extracts the `τ`
coordinate on `𝕊ⁿ × ℝ`. -/
theorem inner_cτ_eq_tau
    (x : SymmMat × ℝ) :
    inner ℝ cτ x = x.2 := by
  rcases x with ⟨H, τ⟩
  -- Unfold the product inner product and cancel the zero matrix component of `cτ`.
  change inner ℝ (0 : SymmMat) H + inner ℝ (1 : ℝ) τ = τ
  simpa using real_inner_eq_mul (1 : ℝ) τ

/-- Helper for Proposition 5.4.5.1: the shape component of an ambient strict barrier point lies
in `𝕊ⁿ₊₊`. -/
theorem ambientPoint_shape_mem
    (x : 𝒟) :
    x.1.1 ∈ (𝕊^n₊₊ : Set SymmMat) := by
  -- The first conjunct of strict ambient-domain membership is exactly strict-cone membership.
  exact ((mem_circumscribedEllipsoidBarrierAmbientDomain_iff a b v x.1.1 x.1.2).1 x.2).1

/-- Helper for Proposition 5.4.5.1: the strict shape component of an ambient strict barrier
point, viewed in the owner carrier `𝕊ⁿ₊₊`. -/
abbrev ambientPointShape
    (x : 𝒟) : 𝕊^n₊₊ :=
  ⟨x.1.1, ambientPoint_shape_mem a b v x⟩

/-- Helper for Proposition 5.4.5.1: the strict shape component of an ambient barrier point has
strictly positive quadratic form on every nonzero vector. -/
theorem ambientPointShapeQuadraticForm_pos
    (x : 𝒟)
    {u : E}
    (hu : u ≠ 0) :
    0 < ⟪(toMatrix (ambientPointShape a b v x)).toEuclideanLin u, u⟫ := by
  -- The strict shape component lies in `𝕊ⁿ₊₊`, so its quadratic form is positive on nonzero
  -- vectors.
  simpa [StrictPositiveSemidefiniteCone.toMatrix_def] using
    (matrix_posDef_iff_forall_inner_pos
      ((ambientPointShape a b v x : 𝕊^n₊₊) : SymmMat)).1
      (strictPositiveSemidefiniteCone_posDef (ambientPointShape a b v x)) u hu

/-- Helper for Proposition 5.4.5.1: every ambient strict barrier point determines an owner
feasible point by weakening the strict slacks to nonstrict feasible-set inequalities. -/
theorem ambientPoint_mem_feasibleSet
    (x : 𝒟) :
    (ambientPointShape a b v x, x.1.2) ∈ (P).feasibleSet := by
  rcases (mem_circumscribedEllipsoidBarrierAmbientDomain_iff a b v x.1.1 x.1.2).1 x.2 with
    ⟨_, hτ, hslack⟩
  rw [mem_circumscribedEllipsoidOptimizationProblem_feasibleSet_iff]
  constructor
  · -- Rewrite the strict epigraph slack as the owner inequality `logDetBarrier n H ≤ τ`.
    have hτ_lt : logDetBarrierAmbient _ x.1.1 < x.1.2 := by
      linarith
    exact le_of_lt (by
      simpa [ambientPointShape, logDetBarrier, logDetBarrierAmbient] using hτ_lt)
  · -- Each strict quadratic slack gives the corresponding nonstrict feasible inequality.
    intro i
    have hslack_le :
        ⟪(x.1.1 : Matrix (Fin _ ) (Fin _) ℝ).toEuclideanLin (a i), a i⟫ ≤
          (b i - ⟪a i, v⟫) ^ (2 : ℕ) := by
      nlinarith [hslack i]
    simpa [StrictPositiveSemidefiniteCone.toMatrix_def] using hslack_le

/-- Helper for Proposition 5.4.5.1: if the strict ambient barrier domain is nonempty, then every
fixed slack square `(b i - ⟪a i, v⟫)^2` is strictly positive. -/
theorem slackSquare_pos_of_strictAmbientDomainNonempty
    (hstrict : Set.Nonempty 𝒟)
    (i : Fin m) :
    0 < (b i - ⟪a i, v⟫) ^ (2 : ℕ) := sorry

/-- The canonical owner feasible point attached to an ambient strict barrier point. -/
def ambientPointToFeasiblePoint
    (x : 𝒟) : (P).feasibleSet :=
  ⟨(ambientPointShape a b v x, x.1.2),
    ambientPoint_mem_feasibleSet a b v x⟩

namespace BarrierPathFollowingScheme

/-- The canonical feasible point determined by the stopping iterate of a
circumscribed-ellipsoid path-following scheme. -/
abbrev stopFeasiblePoint
    {ν : NNReal}
    [IsSelfConcordantBarrierOnWith 𝒟 ν F]
    {β γ ε : ℝ} {x0 : 𝒟}
    (scheme : BarrierPathFollowingScheme cτ F ν x0 β γ ε) :
    (P).feasibleSet :=
  ambientPointToFeasiblePoint a b v
    ⟨scheme scheme.stopIndex, scheme.mem_domain scheme.stopIndex⟩

/-- Helper for Proposition 5.4.5.1: the stopping iterate of a barrier path-following scheme stays
in the ambient barrier domain. -/
theorem stopIterate_mem_domain
    {ν : NNReal}
    [IsSelfConcordantBarrierOnWith 𝒟 ν F]
    {β γ ε : ℝ} {x0 : 𝒟}
    (scheme : BarrierPathFollowingScheme cτ F ν x0 β γ ε) :
    scheme scheme.stopIndex ∈ 𝒟 := by
  -- The scheme keeps every iterate in the domain, so in particular the stopping iterate is
  -- admissible.
  exact scheme.mem_domain scheme.stopIndex

end BarrierPathFollowingScheme

/-- Helper for Proposition 5.4.5.1: shrinking the shape variable of a feasible owner point and
adding the determinant correction to `τ` produces a strict ambient barrier-domain point. -/
theorem scaledFeasiblePoint_mem_barrierAmbientDomain
    (hstrict : Set.Nonempty 𝒟)
    {H : 𝕊^n₊₊} {τ s : ℝ}
    (hfeas : (H, τ) ∈ (P).feasibleSet)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    ((((1 - s) • (H : SymmMat)), τ - (n + 1 : ℝ) * Real.log (1 - s)) :
      SymmMat × ℝ) ∈ 𝒟 := by
  have hfeasFormula :=
    (mem_circumscribedEllipsoidOptimizationProblem_feasibleSet_iff_formula a b v H τ).1 hfeas
  rw [mem_circumscribedEllipsoidBarrierAmbientDomain_iff]
  constructor
  · -- Positive scalar scaling preserves positive definiteness of the shape matrix.
    refine mem_strictPositiveSemidefiniteCone_of_posDef ?_
    simpa [Algebra.smul_def] using
      (strictPositiveSemidefiniteCone_posDef H).smul (sub_pos.mpr hs.2)
  constructor
  · have hdetH_pos : 0 < ((((H : SymmMat) : Mat)).det) := by
      simpa using (strictPositiveSemidefiniteCone_posDef H).det_pos
    have hlog_smul :
        Real.log
            ((((((1 - s) • (H : SymmMat)) : SymmMat) : Mat)).det) =
          (n : ℝ) * Real.log (1 - s) + Real.log ((((H : SymmMat) : Mat)).det) := by
      rw [show ((((((1 - s) • (H : SymmMat)) : SymmMat) : Mat)).det) =
          (1 - s) ^ n * ((((H : SymmMat) : Mat)).det) by
            simpa [Algebra.smul_def] using
              (Matrix.det_smul (((H : SymmMat) : Mat)) (1 - s))]
      rw [Real.log_mul
        (ne_of_gt (show 0 < (1 - s) ^ n by
          exact pow_pos (sub_pos.mpr hs.2) _))
        (ne_of_gt hdetH_pos)]
      rw [← Real.rpow_natCast]
      rw [Real.log_rpow (sub_pos.mpr hs.2)]
    have hbase : 0 ≤ τ + Real.log ((((H : SymmMat) : Mat)).det) := by
      have hτ : -Real.log ((((H : SymmMat) : Mat)).det) ≤ τ := hfeasFormula.1
      linarith
    have hlog_neg : Real.log (1 - s) < 0 := by
      have hs_pos : 0 < 1 - s := sub_pos.mpr hs.2
      have hs_lt_one : 1 - s < 1 := by
        linarith [hs.1]
      exact Real.log_neg hs_pos hs_lt_one
    -- Keep the determinant scaling algebra isolated before finishing by a linear inequality.
    rw [logDetBarrierAmbient_apply, hlog_smul]
    linarith
  · intro i
    by_cases hai : a i = 0
    · -- When `a i = 0`, the scaled quadratic term vanishes and only the fixed slack square remains.
      simpa [hai, Matrix.toEuclideanLin_apply, Matrix.smul_mulVec] using
        slackSquare_pos_of_strictAmbientDomainNonempty a b v hstrict i
    · have hquad_pos :
          0 < ⟪(toMatrix H).toEuclideanLin (a i), a i⟫ := by
        -- Positive definiteness of the owner shape gives strict positivity on every nonzero
        -- direction.
        simpa [StrictPositiveSemidefiniteCone.toMatrix_def] using
          (matrix_posDef_iff_forall_inner_pos ((H : 𝕊^n₊₊) : SymmMat)).1
            (strictPositiveSemidefiniteCone_posDef H) (a i) hai
      have hscaled_qf :
          ⟪((((1 - s) • (H : SymmMat)) : SymmMat) : Mat).toEuclideanLin (a i), a i⟫ =
            (1 - s) * ⟪(toMatrix H).toEuclideanLin (a i), a i⟫ := by
        -- Move the scalar factor through the matrix action before pairing with `a i`.
        simpa [StrictPositiveSemidefiniteCone.toMatrix_def, Matrix.toEuclideanLin_apply,
          Matrix.smul_mulVec] using
          (real_inner_smul_left ((toMatrix H).toEuclideanLin (a i)) (a i) (1 - s))
      -- Rewrite the scaled slack as the feasible slack plus `s` times a positive quadratic form.
      rw [hscaled_qf]
      nlinarith [hfeasFormula.2 i, hquad_pos, hs.1]

/-- Helper for Proposition 5.4.5.1: every feasible owner point lies in the closure of the strict
ambient barrier domain `𝒟`. -/
theorem mem_closure_barrierAmbientDomain_of_mem_feasibleSet
    (hstrict : Set.Nonempty 𝒟)
    (H : 𝕊^n₊₊) (τ : ℝ)
    (hfeas : (H, τ) ∈ (P).feasibleSet) :
    (((H : SymmMat), τ) : SymmMat × ℝ) ∈ closure 𝒟 := by
  let path : ℝ → SymmMat × ℝ := fun s ↦
    ((((1 - s) • (H : SymmMat)), τ - (n + 1 : ℝ) * Real.log (1 - s)) :
      SymmMat × ℝ)
  have hpath :
      Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 (((H : SymmMat), τ) : SymmMat × ℝ)) := by
    have hpath0 : Tendsto path (𝓝 (0 : ℝ)) (𝓝 (path 0)) := by
      have hlogT :
          Tendsto (fun s : ℝ ↦ Real.log (1 - s)) (𝓝 0) (𝓝 (Real.log (1 : ℝ))) := by
        have hinnerT : Tendsto (fun s : ℝ ↦ 1 - s) (𝓝 0) (𝓝 (1 : ℝ)) := by
          simpa using (show ContinuousAt (fun s : ℝ ↦ 1 - s) 0 by fun_prop).tendsto
        exact (Real.continuousAt_log (show (1 : ℝ) ≠ 0 by norm_num)).tendsto.comp hinnerT
      have hlog : ContinuousAt (fun s : ℝ ↦ Real.log (1 - s)) 0 := by
        change Tendsto (fun s : ℝ ↦ Real.log (1 - s)) (𝓝 0) (𝓝 (Real.log (1 - 0)))
        simpa using hlogT
      have hpathCont : ContinuousAt path 0 := by
        have hH : ContinuousAt (fun s : ℝ ↦ (1 - s) • (H : SymmMat)) 0 := by
          fun_prop
        have hτ : ContinuousAt (fun s : ℝ ↦ τ - (n + 1 : ℝ) * Real.log (1 - s)) 0 := by
          exact continuousAt_const.sub (continuousAt_const.mul hlog)
        simpa [path] using hH.prodMk hτ
      exact hpathCont.tendsto
    simpa [path] using
      (hpath0.mono_left nhdsWithin_le_nhds :
        Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 (path 0)))
  have hpath_mem : ∀ᶠ s in 𝓝[>] (0 : ℝ), path s ∈ 𝒟 := by
    have hIoo : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 :=
      Ioo_mem_nhdsGT zero_lt_one
    filter_upwards [hIoo] with s hs
    -- Positive times along the path are strictly feasible by the scaling lemma above.
    exact
      @scaledFeasiblePoint_mem_barrierAmbientDomain m n a b v hstrict H τ s hfeas hs
  -- The strict interior path converges to the original feasible boundary point.
  exact mem_closure_of_tendsto hpath hpath_mem

/-- Helper for Proposition 5.4.5.1: every feasible owner point canonically determines a point of
`closure 𝒟` in the ambient path-following space. -/
def feasiblePointClosure
    (hstrict : Set.Nonempty 𝒟)
    (y : 𝕊^n₊₊ × ℝ)
    (hy : y ∈ (P).feasibleSet) :
    closure 𝒟 :=
  -- Repackage the closure-membership theorem as a canonical ambient closure point.
  ⟨(((y.1 : SymmMat), y.2) : SymmMat × ℝ),
    mem_closure_barrierAmbientDomain_of_mem_feasibleSet a b v hstrict y.1 y.2 hy⟩

/-- Helper for Proposition 5.4.5.1: evaluating `⟪cτ, ·⟫` on the canonical closure point
attached to a feasible owner point recovers the source-facing objective value `τ`. -/
theorem inner_cτ_feasiblePointClosure_eq_objective
    (hstrict : Set.Nonempty 𝒟)
    (y : 𝕊^n₊₊ × ℝ)
    (hy : y ∈ (P).feasibleSet) :
    inner ℝ cτ ((feasiblePointClosure a b v hstrict y hy : closure 𝒟) : SymmMat × ℝ) = P y := by
  -- The closure wrapper keeps the same ambient coordinates, so only the `cτ` pairing and the
  -- owner objective formula need to be unfolded.
  rcases y with ⟨H, τ⟩
  change inner ℝ cτ (((H : SymmMat), τ) : SymmMat × ℝ) = P (H, τ)
  simp [inner_cτ_eq_tau, circumscribedEllipsoidOptimizationProblem_objective_apply]

/-- Helper for Proposition 5.4.5.1: an ambient `cτ`-objective gap estimate implies the
source-facing objective comparison against every owner feasible point. -/
theorem stopTau_le_feasible_add_epsilon_ofOptimalValueGap
    (hstrict : Set.Nonempty 𝒟)
    {ν : NNReal}
    [IsSelfConcordantBarrierOnWith 𝒟 ν F]
    {β γ ε : ℝ}
    {x0 : 𝒟}
    {scheme : BarrierPathFollowingScheme cτ F ν x0 β γ ε}
    (hgap :
      inner ℝ cτ (scheme scheme.stopIndex) - barrierPathFollowingOptimalValue cτ 𝒟 ≤ ε) :
    ∀ y : (P).feasibleSet,
      P (ambientPointToFeasiblePoint a b v
        ⟨scheme scheme.stopIndex, scheme.mem_domain scheme.stopIndex⟩) ≤ P y + ε := by
  intro y
  let yClosure : closure 𝒟 := feasiblePointClosure a b v hstrict y.1 y.2
  -- Compare the stopping iterate with the feasible point after transporting it to `closure 𝒟`.
  have hyOpt :
      barrierPathFollowingOptimalValue cτ 𝒟 ≤ inner ℝ cτ (yClosure : SymmMat × ℝ) :=
    barrierPathFollowingOptimalValue_le_of_mem_closure cτ yClosure
  have hyGap :
      inner ℝ cτ (scheme scheme.stopIndex) ≤
        inner ℝ cτ (yClosure : SymmMat × ℝ) + ε := by
    linarith
  simpa [ambientPointToFeasiblePoint, yClosure,
    inner_cτ_eq_tau, inner_cτ_feasiblePointClosure_eq_objective a b v hstrict y.1 y.2,
    circumscribedEllipsoidOptimizationProblem_objective_apply] using hyGap

/-- Helper for Proposition 5.4.5.1: once the barrier-side short-step package supplies the
stopping bound and the ambient `cτ`-objective gap, the source-facing stop specification follows
immediately. -/
theorem instantiateCircumscribedEllipsoidPathFollowingPackage
    (hstrict : Set.Nonempty 𝒟)
    (hmn_pos : 0 < (m + n : ℝ))
    {ν : NNReal}
    [IsSelfConcordantBarrierOnWith 𝒟 ν F]
    {β γ ε : ℝ}
    {C : NNRealˣ}
    {x0 : 𝒟}
    {scheme : BarrierPathFollowingScheme cτ F ν x0 β γ ε}
    (hβ : β < 1 / 2)
    (hγ : 0 < γ)
    (hbound :
      scheme.stopIndex ≤
        ⌈((C : NNReal) : ℝ) * Real.sqrt (m + n + 1 : ℝ) *
          Real.log ((m + n : ℝ) / ε)⌉₊)
    (hgap :
      inner ℝ cτ (scheme scheme.stopIndex) - barrierPathFollowingOptimalValue cτ 𝒟 ≤ ε) :
    ∃ hstopApprox :
        (P).IsApproximateMinimizer ε
          (ambientPointToFeasiblePoint a b v
            ⟨scheme scheme.stopIndex, scheme.mem_domain scheme.stopIndex⟩),
      scheme.stopIndex ≤
        ⌈((C : NNReal) : ℝ) * Real.sqrt (m + n + 1 : ℝ) *
          Real.log ((m + n : ℝ) / ε)⌉₊ := sorry

/-- An auxiliary owner-style summary record for circumscribed-ellipsoid path-following output,
retaining only the returned feasible point of `P`, its owner-level `ε`-approximate-minimizer
certificate, and the displayed logarithmic stopping bound. The raw ambient
`BarrierPathFollowingScheme` witness stays private to the helper layer. -/
structure CircumscribedEllipsoidPathFollowingScheme
    (ε : ℝ)
    (C : NNRealˣ) where
  /-- The feasible point of `P` returned by the path-following method. -/
  stopPoint : (P).feasibleSet
  /-- The returned feasible point is `ε`-accurate for the owner optimization problem `P`. -/
  stopApprox :
    (P).IsApproximateMinimizer ε stopPoint
  /-- The number of path-following iterations used to produce `stopPoint`. -/
  stopIndex : ℕ
  /-- The stopping index satisfies the displayed
  `O(√(m + n + 1) log ((m + n) / ε))` bound. -/
  stopIndex_le :
    stopIndex ≤
      ⌈((C : NNReal) : ℝ) * Real.sqrt (m + n + 1 : ℝ) *
        Real.log ((m + n : ℝ) / ε)⌉₊

/-- Helper for Proposition 5.4.5.1: the remaining blocker is the barrier-specific private
short-step package that should supply one uniform constant `C` together with, for each
`ε ∈ (0, 1)`, one source-facing circumscribed-ellipsoid output package whose stopping point
admits the owner-level `ε`-approximate-minimizer certificate and satisfies the displayed
logarithmic stopping bound. -/
private theorem existsAmbientShortStepPackageOfOptimalValueGap
    {ν : NNReal}
    [IsSelfConcordantBarrierOnWith 𝒟 ν F]
    (hmn_pos : 0 < (m + n : ℝ))
    (hstrict : Set.Nonempty 𝒟)
    (hoptimal : (P).optimalValue ≠ ⊥)
    (hν : ν ≤ (m + n + 1 : NNReal)) :
    ∃ C : NNRealˣ,
      ∀ {ε : ℝ}, 0 < ε → ε < 1 →
        Nonempty (CircumscribedEllipsoidPathFollowingScheme (m := m) (n := n) a b v ε C) :=
  sorry

-- Semantic recall note: a `lean_leansearch` query for a reusable barrier-path-following
-- specialization surfaced only unrelated generic hits, so the public proposition is stated as the
-- source-facing output record promised by the text, while the raw short-step parameters and
-- ambient scheme stay in the private helper layer.
/-- Proposition 5.4.5.1: let `F(H, τ)` be a `ν`-self-concordant barrier for the
circumscribed-ellipsoid problem, with `ν ≤ m + n + 1`. Then there exists a positive iteration
constant `C`, uniform in the target accuracy `ε ∈ (0, 1)`, such that for every such `ε` the
path-following method returns a source-facing circumscribed-ellipsoid output package whose
stopping point is `ε`-accurate for the owner problem and whose Newton-iteration count satisfies
the displayed `O(√(m + n + 1) log ((m + n) / ε))` bound, provided the strict ambient barrier
domain is nonempty and the owner optimal value is finite. -/
theorem exists_circumscribedEllipsoidPathFollowingScheme
    {ν : NNReal}
    [IsSelfConcordantBarrierOnWith 𝒟 ν F]
    (hmn_pos : 0 < (m + n : ℝ))
    (hstrict : Set.Nonempty 𝒟)
    (hoptimal : (P).optimalValue ≠ ⊥)
    (hν : ν ≤ (m + n + 1 : NNReal)) :
    ∃ C : NNRealˣ,
      ∀ {ε : ℝ}, 0 < ε → ε < 1 →
        Nonempty (CircumscribedEllipsoidPathFollowingScheme (m := m) (n := n) a b v ε C) := sorry

end
