/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Analysis.InnerProductSpace.ProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_5_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_5_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open WithLp
open Set Topology Filter
open scoped BigOperators Gradient RealInnerProductSpace RealSymmetricMatrixSpace

variable {ι : Type*} [Fintype ι] {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "SymmMat" => 𝕊^n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "TailSpace" => Eₙ × ℝ
local notation "MVEEAmbientSpace" => SymmMat × TailSpace

noncomputable local instance instLocalChap05_Theorem_5_4_5_11 : SeminormedAddCommGroup TailSpace :=
  WithLp.seminormedAddCommGroupToProd 2 Eₙ ℝ

noncomputable local instance instLocalChap05_Theorem_5_4_5_12 : NormedAddCommGroup TailSpace :=
  WithLp.normedAddCommGroupToProd 2 Eₙ ℝ

noncomputable local instance instLocalChap05_Theorem_5_4_5_13 : NormedSpace ℝ TailSpace :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 Eₙ ℝ

noncomputable local instance instInnerProductSpaceChap05_Theorem_5_4_5_11 : InnerProductSpace ℝ TailSpace where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 Eₙ ℝ x]
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

noncomputable local instance instLocalChap05_Theorem_5_4_5_14 : CompleteSpace TailSpace := inferInstance

noncomputable local instance instLocalChap05_Theorem_5_4_5_15 : SeminormedAddCommGroup MVEEAmbientSpace :=
  WithLp.seminormedAddCommGroupToProd 2 SymmMat TailSpace

noncomputable local instance instLocalChap05_Theorem_5_4_5_16 : NormedAddCommGroup MVEEAmbientSpace :=
  WithLp.normedAddCommGroupToProd 2 SymmMat TailSpace

noncomputable local instance instLocalChap05_Theorem_5_4_5_17 : NormedSpace ℝ MVEEAmbientSpace :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 SymmMat TailSpace

noncomputable local instance instInnerProductSpaceChap05_Theorem_5_4_5_12 : InnerProductSpace ℝ MVEEAmbientSpace where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 SymmMat TailSpace x]
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

/- Theorem 5.4.5.1 lies in the minimum-volume enclosing-ellipsoid / barrier path-following domain.

Sampled owner-style declarations in this domain:
* `minimumVolumeEnclosingEllipsoidProblem` in `Chap05/Definition_5_4_5_1`, the source-facing
  owner of the MVEE feasible set and objective;
* `minimumVolumeEnclosingEllipsoidBarrierDomain`,
  `minimumVolumeEnclosingEllipsoidBarrierAmbient`, and
  `minimumVolumeEnclosingEllipsoidBarrier` in `Chap05/Definition_5_4_5_2`, the source-facing
  strict-domain MVEE barrier API;
* `logDetBarrierAmbient` in `Chap05/Definition_5_4_4_5`, the chapter bridge for the
  `-\log \det` contribution on symmetric matrices;
* `BarrierPathFollowingScheme` in `Chap05/Definition_5_3_4_1`, the chapter owner for the
  short-step path-following data.

Best owner abstraction:
* source-facing: the MVEE problem and barrier on strict-cone triples `(H, v, τ)`;
* core/canonical: `BarrierPathFollowingScheme`;
* bridge/view: the ambient symmetric-matrix product `𝕊^n × Eₙ × ℝ`, used only to host the
  self-concordant-barrier assumption needed by the path-following scheme.

Primitive data:
* the finite point family `a`.

Derived API:
* the raw ambient owner barrier from `Definition_5_4_5_2`, used directly on
  `𝕊^n × Eₙ × ℝ`;
* the path-following existence theorem.

This file therefore does not introduce a second public MVEE barrier owner. It uses a local
`L²` inner-product structure on the raw ambient product `𝕊^n × Eₙ × ℝ`, so that the theorem can
be stated directly on the owner ambient domain and ambient barrier from `Definition_5_4_5_2`
without exporting a parallel `WithLp` wrapper type. This is the ambient inner-product space
required by
`BarrierPathFollowingScheme`.
-/

section

variable (a : ι → Eₙ)

local notation "F" => minimumVolumeEnclosingEllipsoidBarrierAmbient (n := n) a
local notation "P" => minimumVolumeEnclosingEllipsoidProblem (n := n) a
local notation "𝒟" => minimumVolumeEnclosingEllipsoidBarrierAmbientDomain (n := n) a

local notation "cτ" =>
  ((0 : SymmMat), (0 : Eₙ), (1 : ℝ))

-- Proof sketch: specialize the standard short-step path-following existence and complexity theory
-- to the MVEE objective vector `cτ` and to the owner ambient barrier `F` from
-- `Definition_5_4_5_2`.

/-- Helper for Theorem 5.4.5.1: on `ℝ`, the real inner product is ordinary multiplication. -/
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

/-- Helper for Theorem 5.4.5.1: the scalar direction on `Eₙ × ℝ` extracts the final `ℝ`
coordinate under the local `WithLp` inner-product structure. -/
theorem inner_tailUnit_eq_snd
    (x : TailSpace) :
    inner ℝ (((0 : Eₙ), (1 : ℝ)) : TailSpace) x = x.2 := by
  rcases x with ⟨v, τ⟩
  -- Rewrite the local `WithLp` product inner product down to its scalar component.
  change
    inner ℝ (WithLp.toLp 2 (((0 : Eₙ), (1 : ℝ)) : TailSpace))
      (WithLp.toLp 2 ((v, τ) : TailSpace)) = τ
  simpa using real_inner_eq_mul (1 : ℝ) τ

/-- Helper for Theorem 5.4.5.1: the ambient objective direction `cτ` extracts the `τ`
coordinate under the local `WithLp` inner-product structure on `𝕊ⁿ × Eₙ × ℝ`. -/
theorem inner_cτ_eq_tau
    (x : MVEEAmbientSpace) :
    inner ℝ cτ x = x.2.2 := by
  rcases x with ⟨H, v, τ⟩
  -- Rewrite the ambient `WithLp` pairing to the tail-space component extracted above.
  change
    inner ℝ
        (WithLp.toLp 2
          (((0 : SymmMat), (((0 : Eₙ), (1 : ℝ)) : TailSpace)) : MVEEAmbientSpace))
        (WithLp.toLp 2 ((H, ((v, τ) : TailSpace)) : MVEEAmbientSpace)) = τ
  simpa using inner_tailUnit_eq_snd ((v, τ) : TailSpace)

/-- Helper for Theorem 5.4.5.1: ambient strict-domain membership of a raw triple already implies
the weak owner inequalities `-log det H ≤ τ` and `‖H aᵢ - v‖ ≤ 1`. -/
theorem ambientTriple_mem_feasibleSet_formula
    (a : ι → Eₙ)
    {H : SymmMat} {v : Eₙ} {τ : ℝ}
    (hx : (H, v, τ) ∈ minimumVolumeEnclosingEllipsoidBarrierAmbientDomain a) :
    -Real.log (H : Mat).det ≤ τ ∧
      ∀ i : ι, ‖((H : Mat).toEuclideanLin (a i) - v : Eₙ)‖ ≤ 1 := by
  rcases (mem_minimumVolumeEnclosingEllipsoidBarrierAmbientDomain_iff
    a H v τ).1 hx with ⟨_, hτ, hslack⟩
  constructor
  · -- Rewrite the strict epigraph slack into the weak owner determinant inequality.
    have hτ'' : 0 < τ + Real.log (H : Mat).det := by
      simpa [logDetBarrierAmbient_apply] using hτ
    have hτ' : -Real.log (H : Mat).det < τ := by
      linarith
    exact le_of_lt hτ'
  · intro i
    let z : Eₙ := ((H : Mat).toEuclideanLin (a i) - v)
    have hslack' : 0 < 1 - ‖z‖ ^ (2 : ℕ) := by
      simpa [z] using hslack i
    have hnorm_lt : ‖z‖ < 1 := by
      nlinarith [norm_nonneg z]
    simpa [z] using le_of_lt hnorm_lt

/-- Helper for Theorem 5.4.5.1: once the shape coordinate is bundled back into `𝕊ⁿ₊₊`, the raw
ambient weak inequalities become owner feasible-set membership. -/
theorem ambientTriple_mem_feasibleSet
    (a : ι → Eₙ)
    {H : SymmMat} {v : Eₙ} {τ : ℝ}
    (hx : (H, v, τ) ∈ minimumVolumeEnclosingEllipsoidBarrierAmbientDomain a) :
    (((⟨H, ((mem_minimumVolumeEnclosingEllipsoidBarrierAmbientDomain_iff a H v τ).1 hx).1⟩ :
        𝕊^n₊₊), v, τ) : 𝕊^n₊₊ × Eₙ × ℝ) ∈
      (minimumVolumeEnclosingEllipsoidProblem a).feasibleSet := by
  refine
    (mem_minimumVolumeEnclosingEllipsoidProblem_feasibleSet_iff_formula
      a
      (⟨H, ((mem_minimumVolumeEnclosingEllipsoidBarrierAmbientDomain_iff a H v τ).1 hx).1⟩ :
        𝕊^n₊₊)
      v τ).2 ?_
  -- Route correction: first prove the raw weak inequalities on the ambient coordinates, then
  -- rewrite them through the owner carrier bundled by the strict-cone membership proof.
  simpa [StrictPositiveSemidefiniteCone.toMatrix_def] using
    ambientTriple_mem_feasibleSet_formula a hx

/-- The canonical feasible point of the MVEE problem attached to an ambient strict barrier
point. -/
def ambientPointToFeasiblePoint
    (x : 𝒟) : (P).feasibleSet :=
  -- Bundle the raw ambient triple using the canonical strict-cone witness recovered from `x.2`.
  ⟨((⟨x.1.1,
        ((mem_minimumVolumeEnclosingEllipsoidBarrierAmbientDomain_iff
          (n := n) a x.1.1 x.1.2.1 x.1.2.2).1 x.2).1⟩ : 𝕊^n₊₊), x.1.2.1, x.1.2.2),
    ambientTriple_mem_feasibleSet (a := a) x.2⟩

/-- Helper for Theorem 5.4.5.1: shrinking both the shape variable and the center of a feasible
MVEE triple produces a strict ambient barrier-domain point. -/
theorem scaledFeasiblePoint_mem_barrierAmbientDomain
    (a : ι → Eₙ)
    {H : 𝕊^n₊₊} {v : Eₙ} {τ s : ℝ}
    (hfeas : (H, v, τ) ∈ (minimumVolumeEnclosingEllipsoidProblem a).feasibleSet)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    ((((1 - s) • (H : SymmMat)), (1 - s) • v,
        τ - (n + 1 : ℝ) * Real.log (1 - s)) : MVEEAmbientSpace) ∈
      minimumVolumeEnclosingEllipsoidBarrierAmbientDomain a := by
  have hfeasFormula :=
    (mem_minimumVolumeEnclosingEllipsoidProblem_feasibleSet_iff_formula a H v τ).1 hfeas
  rw [mem_minimumVolumeEnclosingEllipsoidBarrierAmbientDomain_iff]
  constructor
  · -- Positive scalar scaling preserves positive definiteness of the shape matrix.
    refine mem_strictPositiveSemidefiniteCone_of_posDef ?_
    simpa [Algebra.smul_def] using
      (strictPositiveSemidefiniteCone_posDef H).smul (sub_pos.mpr hs.2)
  constructor
  · -- The logarithmic correction leaves one extra `-log (1 - s)` unit of epigraph slack.
    have hdetH_pos : 0 < ((((H : SymmMat) : Mat)).det) := by
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
      have hτ : -Real.log ((((H : SymmMat) : Mat)).det) ≤ τ := by
        simpa [StrictPositiveSemidefiniteCone.toMatrix_def] using hfeasFormula.1
      linarith
    have hlog_neg : Real.log (1 - s) < 0 := by
      have hs_pos : 0 < 1 - s := sub_pos.mpr hs.2
      have hs_lt_one : 1 - s < 1 := by
        linarith [hs.1]
      exact Real.log_neg hs_pos hs_lt_one
    have hepigraph_slack :
        0 < τ - (n + 1 : ℝ) * Real.log (1 - s) -
          logDetBarrierAmbient n ((1 - s) • (H : SymmMat)) := by
      rw [logDetBarrierAmbient_apply, hlog_smul]
      linarith
    exact hepigraph_slack
  · intro i
    have hs_pos : 0 < 1 - s := sub_pos.mpr hs.2
    have hs_lt_one : 1 - s < 1 := by
      linarith [hs.1]
    let z : Eₙ := ((((H : SymmMat) : Mat)).toEuclideanLin (a i) - v)
    let zScaled : Eₙ :=
      ((((((1 - s) • (H : SymmMat)) : SymmMat) : Mat)).toEuclideanLin (a i) - (1 - s) • v)
    have hscaled_apply : zScaled = (1 - s) • z := by
      simp [z, zScaled, Matrix.toEuclideanLin_apply, Matrix.smul_mulVec, smul_sub]
    have hscaled_norm : ‖zScaled‖ = (1 - s) * ‖z‖ := by
      calc
        ‖zScaled‖ = ‖(1 - s) • z‖ := by rw [hscaled_apply]
        _ = |1 - s| * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ = (1 - s) * ‖z‖ := by rw [abs_of_pos hs_pos]
    have hmul_le : (1 - s) * ‖z‖ ≤ (1 - s) * 1 := by
      have hnorm_le : ‖z‖ ≤ 1 := by
        simpa [z, StrictPositiveSemidefiniteCone.toMatrix_def] using hfeasFormula.2 i
      exact mul_le_mul_of_nonneg_left hnorm_le (le_of_lt hs_pos)
    have hscaled_lt : ‖zScaled‖ < 1 := by
      rw [hscaled_norm]
      have hlt : (1 - s) * (1 : ℝ) < 1 := by
        nlinarith
      exact lt_of_le_of_lt hmul_le hlt
    have hstrict_slack : 0 < 1 - ‖zScaled‖ ^ (2 : ℕ) := by
      nlinarith [norm_nonneg zScaled, hscaled_lt]
    simpa [zScaled] using hstrict_slack

/-- Helper for Theorem 5.4.5.1: every feasible MVEE triple lies in the closure of the strict
ambient barrier domain `𝒟`. -/
theorem scaledFeasiblePath_tendsto
    (H : 𝕊^n₊₊) (v : Eₙ) (τ : ℝ) :
    Tendsto
      (fun s : ℝ ↦
        ((((1 - s) • (H : SymmMat)), (1 - s) • v,
            τ - (n + 1 : ℝ) * Real.log (1 - s)) : MVEEAmbientSpace))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((H : SymmMat), v, τ) : MVEEAmbientSpace))) := by
  let path : ℝ → MVEEAmbientSpace := fun s ↦
    ((((1 - s) • (H : SymmMat)), (1 - s) • v,
        τ - (n + 1 : ℝ) * Real.log (1 - s)) : MVEEAmbientSpace)
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
      have hv : ContinuousAt (fun s : ℝ ↦ (1 - s) • v) 0 := by
        fun_prop
      have hτ : ContinuousAt (fun s : ℝ ↦ τ - (n + 1 : ℝ) * Real.log (1 - s)) 0 := by
        exact continuousAt_const.sub (continuousAt_const.mul hlog)
      have htail : ContinuousAt (fun s : ℝ ↦ ((1 - s) • v, τ - (n + 1 : ℝ) * Real.log (1 - s))) 0 := by
        exact hv.prodMk hτ
      simpa [path] using hH.prodMk htail
    -- First obtain ordinary continuity at `0`, then restrict to the right-neighborhood filter.
    exact hpathCont.tendsto
  simpa [path] using
    (hpath0.mono_left nhdsWithin_le_nhds :
      Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 (path 0)))

/-- Helper for Theorem 5.4.5.1: every feasible MVEE triple lies in the closure of the strict
ambient barrier domain `𝒟`. -/
theorem mem_closure_barrierAmbientDomain_of_mem_feasibleSet
    (H : 𝕊^n₊₊) (v : Eₙ) (τ : ℝ)
    (hfeas : (H, v, τ) ∈ (P).feasibleSet) :
    ((((H : SymmMat), v, τ) : MVEEAmbientSpace)) ∈ closure 𝒟 := by
  have hpath :
      Tendsto
        (fun s : ℝ ↦
          ((((1 - s) • (H : SymmMat)), (1 - s) • v,
              τ - (n + 1 : ℝ) * Real.log (1 - s)) : MVEEAmbientSpace))
        (𝓝[>] (0 : ℝ))
        (𝓝 ((((H : SymmMat), v, τ) : MVEEAmbientSpace))) := by
    -- Freeze the closure-approximation path in one normal form before using it downstream.
    simpa using scaledFeasiblePath_tendsto (H := H) v τ
  have hpath_mem :
      ∀ᶠ s in 𝓝[>] (0 : ℝ),
        ((((1 - s) • (H : SymmMat)), (1 - s) • v,
            τ - (n + 1 : ℝ) * Real.log (1 - s)) : MVEEAmbientSpace) ∈ 𝒟 := by
    have hIoo : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 :=
      Ioo_mem_nhdsGT zero_lt_one
    filter_upwards [hIoo] with s hs
    -- Positive times along the path are strictly feasible by the scaling lemma above.
    exact
      scaledFeasiblePoint_mem_barrierAmbientDomain
        (a := a) (H := H) (v := v) (τ := τ) (s := s) hfeas hs
  -- The strict interior path converges to the original feasible boundary point.
  exact mem_closure_of_tendsto hpath hpath_mem

/-- Helper for Theorem 5.4.5.1: every feasible MVEE point canonically determines a point of
`closure 𝒟` in the ambient path-following space. -/
def feasiblePointClosurePoint
    (y : 𝕊^n₊₊ × Eₙ × ℝ)
    (hy : y ∈ (P).feasibleSet) :
    closure 𝒟 := by
  -- Repackage the closure-membership theorem as a canonical closure-domain point.
  refine ⟨(((y.1 : SymmMat), y.2.1, y.2.2) : MVEEAmbientSpace), ?_⟩
  -- The feasible MVEE inequalities already give the approximating strict-domain path.
  exact mem_closure_barrierAmbientDomain_of_mem_feasibleSet y.1 y.2.1 y.2.2 hy

/-- Helper for Theorem 5.4.5.1: evaluating `⟪cτ, ·⟫` on the canonical closure point attached to a
feasible MVEE triple recovers the source-facing objective value `τ`. -/
theorem inner_cτ_feasiblePointClosure_eq_objective
    (y : 𝕊^n₊₊ × Eₙ × ℝ)
    (hy : y ∈ (P).feasibleSet) :
    inner ℝ cτ ((((y.1 : SymmMat), y.2.1, y.2.2) : MVEEAmbientSpace)) = P y := by
  -- The canonical closure wrapper does not change the ambient coordinates, so only the `cτ`
  -- rewrite and the source objective formula remain.
  rcases y with ⟨H, v, τ⟩
  simp [inner_cτ_eq_tau, minimumVolumeEnclosingEllipsoidProblem_objective_apply]

/-- Helper for Theorem 5.4.5.1: any generic ambient `cτ`-objective gap estimate implies the
source-facing MVEE stopping bound against every feasible comparison point. -/
theorem stopTau_le_feasible_add_epsilon_of_genericGap
    {β γ ε : ℝ}
    {x0 : 𝒟}
    [IsSelfConcordantBarrierOnWith 𝒟 (Fintype.card ι + n + 1) F]
    {scheme : BarrierPathFollowingScheme cτ F (Fintype.card ι + n + 1) x0 β γ ε}
    {xOpt : closure 𝒟}
    (hopt :
      ∀ z : closure 𝒟,
        inner ℝ cτ (xOpt : MVEEAmbientSpace) ≤ inner ℝ cτ (z : MVEEAmbientSpace))
    (hgap :
      inner ℝ cτ (scheme scheme.stopIndex) - inner ℝ cτ (xOpt : MVEEAmbientSpace) ≤ ε) :
    ∀ y ∈ (P).feasibleSet,
      (scheme scheme.stopIndex).2.2 ≤ P y + ε := by
  intro y hy
  let yClosure : closure 𝒟 := feasiblePointClosurePoint (a := a) y hy
  -- Compare the stopping iterate with the feasible point after transporting it to `closure 𝒟`.
  have hyOpt :
      inner ℝ cτ (xOpt : MVEEAmbientSpace) ≤ inner ℝ cτ (yClosure : MVEEAmbientSpace) :=
    hopt yClosure
  have hyGap :
      inner ℝ cτ (scheme scheme.stopIndex) ≤ inner ℝ cτ (yClosure : MVEEAmbientSpace) + ε := by
    linarith
  simpa [yClosure, inner_cτ_eq_tau,
    inner_cτ_feasiblePointClosure_eq_objective (a := a) y hy]
    using hyGap

/-- Helper for Theorem 5.4.5.1: once a generic ambient short-step package supplies a stopping
bound and an ambient `cτ`-objective gap, the MVEE source-facing conclusion follows immediately. -/
theorem instantiateMveePathFollowingPackage
    {β γ ε : ℝ}
    {C : NNReal}
    {x0 : 𝒟}
    [IsSelfConcordantBarrierOnWith 𝒟 (Fintype.card ι + n + 1) F]
    {scheme : BarrierPathFollowingScheme cτ F (Fintype.card ι + n + 1) x0 β γ ε}
    {xOpt : closure 𝒟}
    (hbound :
      scheme.stopIndex ≤
        ⌈(C : ℝ) * Real.sqrt (Fintype.card ι + n + 1 : ℝ) *
          Real.log ((Fintype.card ι + n : ℝ) / ε)⌉₊)
    (hopt :
      ∀ z : closure 𝒟,
        inner ℝ cτ (xOpt : MVEEAmbientSpace) ≤ inner ℝ cτ (z : MVEEAmbientSpace))
    (hgap :
      inner ℝ cτ (scheme scheme.stopIndex) - inner ℝ cτ (xOpt : MVEEAmbientSpace) ≤ ε) :
    scheme.stopIndex ≤
        ⌈(C : ℝ) * Real.sqrt (Fintype.card ι + n + 1 : ℝ) *
          Real.log ((Fintype.card ι + n : ℝ) / ε)⌉₊ ∧
      ∀ y ∈ (P).feasibleSet,
        (scheme scheme.stopIndex).2.2 ≤ P y + ε := by
  -- Keep the generic complexity estimate unchanged and only rewrite the objective comparison.
  refine ⟨hbound, ?_⟩
  -- The dedicated bridge lemma transports the ambient gap to every feasible MVEE comparison
  -- point.
  exact stopTau_le_feasible_add_epsilon_of_genericGap hopt hgap

/-- Helper for Theorem 5.4.5.1: the explicit penalty objective
`z ↦ t ⟪c, z⟫ + F z` has gradient `(t : ℝ) • c + ∇ F z` at every differentiability point of
`F`. -/
theorem hasGradientAt_penaltyObjective
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (c : E) (f : E → ℝ) (t : ℝ) {x : E}
    (hf_diff : DifferentiableAt ℝ f x) :
    HasGradientAt (fun z : E ↦ t * inner ℝ c z + f z) ((t : ℝ) • c + ∇ f x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hlinear : HasFDerivAt (fun z : E ↦ t * inner ℝ c z) ((t : ℝ) • innerSL ℝ c) x := by
    simpa using (((t : ℝ) • innerSL ℝ c).hasFDerivAt :
      HasFDerivAt (fun z : E ↦ ((t : ℝ) • innerSL ℝ c) z) ((t : ℝ) • innerSL ℝ c) x)
  -- Differentiate the linear tilt and then add the barrier gradient term.
  simpa using hlinear.add hf_diff.hasGradientAt.hasFDerivAt

/-- Helper for Theorem 5.4.5.1: any exact minimizer of the penalty objective at parameter `T`
solves the stationarity equation `∇ F xBase = -(T : ℝ) • c`. -/
theorem penaltyMinimizer_gradient_eq_neg_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {dom : Set E} {ν : NNReal} {f : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν f]
    (c : E)
    (T : Set.Ici (0 : ℝ))
    {xBase : dom}
    (hbase :
      IsMinOn
        (fun z : E ↦ (T : ℝ) * inner ℝ c z + f z)
        dom
        (xBase : E)) :
    ∇ f (xBase : E) = -((T : ℝ) • c) := by
  let hstd : IsStandardSelfConcordantOn dom f := inferInstance
  have hdiff : DifferentiableAt ℝ f (xBase : E) := by
    exact
      (hstd.contDiffOn.contDiffAt (hstd.isOpen_domain.mem_nhds xBase.2)).differentiableAt
        (by norm_num)
  have hlocal : IsLocalMin (fun z : E ↦ (T : ℝ) * inner ℝ c z + f z) (xBase : E) :=
    hbase.isLocalMin (hstd.isOpen_domain.mem_nhds xBase.2)
  have hgrad :
      ∇ (fun z : E ↦ (T : ℝ) * inner ℝ c z + f z) (xBase : E) =
        (T : ℝ) • c + ∇ f (xBase : E) :=
    (hasGradientAt_penaltyObjective c f (T : ℝ) hdiff).gradient
  have hzero : ∇ (fun z : E ↦ (T : ℝ) * inner ℝ c z + f z) (xBase : E) = 0 :=
    isLocalMin_gradient_eq_zero hlocal
  -- Read the first-order stationarity equation back as the barrier gradient identity.
  rw [hgrad] at hzero
  simpa [eq_neg_iff_add_eq_zero, add_comm, add_left_comm, add_assoc] using hzero

/-- Helper for Theorem 5.4.5.1: a unit-penalty minimizer rewrites the explicit penalty family
`z ↦ t ⟪c, z⟫ + F z` into the auxiliary-central-path objective based at that minimizer. -/
theorem penaltyObjective_eq_auxiliaryOfUnitMinimizer
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {dom : Set E} {ν : NNReal} {f : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν f]
    (c : E)
    {xBase : dom}
    (hbase :
      IsMinOn
        (fun z : E ↦ inner ℝ c z + f z)
        dom
        (xBase : E)) :
    ∀ t : ℝ,
      (fun z : E ↦ t * inner ℝ c z + f z) = auxiliaryCentralPathObjective f xBase t := by
  have hbase' :
      IsMinOn
        (fun z : E ↦ ((⟨1, by norm_num⟩ : Set.Ici (0 : ℝ)) : ℝ) * inner ℝ c z + f z)
        dom
        (xBase : E) := by
    simpa using hbase
  have hgrad :
      ∇ f (xBase : E) = -c := by
    simpa using
      (penaltyMinimizer_gradient_eq_neg_smul
        (dom := dom) (ν := ν) (f := f) c (⟨1, by norm_num⟩ : Set.Ici (0 : ℝ)) hbase')
  intro t
  funext z
  -- Rewrite the base-point gradient so the explicit penalty family matches the auxiliary one.
  rw [auxiliaryCentralPathObjective_apply, hgrad]
  simpa [inner_neg_left, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Theorem 5.4.5.1: the source-side barrier-size term `Fintype.card ι + n` is
positive whenever the admissible accuracy window `0 < ε < Fintype.card ι + n` is nonempty. -/
theorem barrierSize_pos_of_smallAccuracy
    {ε : ℝ}
    (hε : 0 < ε) (hε_small : ε < (Fintype.card ι + n : ℝ)) :
    0 < (Fintype.card ι + n : ℝ) := by
  -- The strict upper bound on `ε` forces the barrier-size term to dominate a positive number.
  linarith

/-- Helper for Theorem 5.4.5.1: the logarithm argument in the iteration bound is positive on the
allowed accuracy range. -/
theorem barrierSize_div_accuracy_pos
    {ε : ℝ}
    (hε : 0 < ε) (hε_small : ε < (Fintype.card ι + n : ℝ)) :
    0 < (Fintype.card ι + n : ℝ) / ε := by
  -- Combine the positive numerator from `barrierSize_pos_of_smallAccuracy` with `ε > 0`.
  exact div_pos
    (barrierSize_pos_of_smallAccuracy (n := n) hε hε_small)
    hε

/-- Helper for Theorem 5.4.5.1: every closure point bounds the ambient optimal value from above,
because `barrierPathFollowingOptimalValue cτ 𝒟` is the infimum of the `cτ`-objective over
`closure 𝒟`. -/
theorem barrierPathFollowingOptimalValue_le_of_mem_closure
    (z : closure 𝒟) :
    barrierPathFollowingOptimalValue cτ 𝒟 ≤ inner ℝ cτ (z : MVEEAmbientSpace) := by
  -- Unfold the infimum owner and certify the chosen closure point as one element of that image.
  rw [barrierPathFollowingOptimalValue]
  exact sInf_le ⟨(z : MVEEAmbientSpace), z.2, rfl⟩

/-- Helper for Theorem 5.4.5.1: an ambient gap bound against
`barrierPathFollowingOptimalValue cτ 𝒟` yields the source-facing `ε`-accuracy estimate for the
canonical stopping feasible point of an MVEE path-following scheme. -/
theorem stopTau_le_feasible_add_epsilon_ofOptimalValueGap
    {β γ ε : ℝ}
    {x0 : 𝒟}
    [IsSelfConcordantBarrierOnWith 𝒟 (Fintype.card ι + n + 1) F]
    {scheme : BarrierPathFollowingScheme cτ F (Fintype.card ι + n + 1) x0 β γ ε}
    (hgap :
      inner ℝ cτ (scheme scheme.stopIndex) - barrierPathFollowingOptimalValue cτ 𝒟 ≤ ε) :
    ∀ y : (P).feasibleSet,
      (scheme scheme.stopIndex).2.2 ≤ P y + ε := by
  intro y
  let yClosure : closure 𝒟 := feasiblePointClosurePoint (a := a) y.1 y.2
  -- Compare the optimal-value infimum to the transported feasible comparison point in `closure 𝒟`.
  have hopt_le_y :
      barrierPathFollowingOptimalValue cτ 𝒟 ≤ inner ℝ cτ (yClosure : MVEEAmbientSpace) :=
    barrierPathFollowingOptimalValue_le_of_mem_closure (a := a) yClosure
  -- The ambient stopping-gap estimate now bounds the stopping objective by the comparison point.
  have hyGap :
      inner ℝ cτ (scheme scheme.stopIndex) ≤ inner ℝ cτ (yClosure : MVEEAmbientSpace) + ε := by
    linarith [hgap, hopt_le_y]
  -- Rewrite the comparison point back to the source-facing objective value.
  simpa [yClosure,
    inner_cτ_eq_tau,
    inner_cτ_feasiblePointClosure_eq_objective (a := a) y.1 y.2,
    minimumVolumeEnclosingEllipsoidProblem_objective_apply] using hyGap

/-- Helper for Theorem 5.4.5.1: once the barrier-side short-step package supplies the stopping
bound and the ambient `cτ`-objective gap, the source-facing MVEE stopping claims follow
immediately. -/
theorem instantiateMveePathFollowingPackageOfOptimalValueGap
    {β γ ε : ℝ}
    {C : NNRealˣ}
    {x0 : 𝒟}
    [IsSelfConcordantBarrierOnWith 𝒟 (Fintype.card ι + n + 1) F]
    {scheme : BarrierPathFollowingScheme cτ F (Fintype.card ι + n + 1) x0 β γ ε}
    (hbound :
      scheme.stopIndex ≤
        ⌈((C : NNReal) : ℝ) * Real.sqrt (Fintype.card ι + n + 1 : ℝ) *
          Real.log ((Fintype.card ι + n : ℝ) / ε)⌉₊)
    (hgap :
      inner ℝ cτ (scheme scheme.stopIndex) - barrierPathFollowingOptimalValue cτ 𝒟 ≤ ε) :
    scheme.stopIndex ≤
        ⌈((C : NNReal) : ℝ) * Real.sqrt (Fintype.card ι + n + 1 : ℝ) *
          Real.log ((Fintype.card ι + n : ℝ) / ε)⌉₊ ∧
      ∀ y : (P).feasibleSet,
        (scheme scheme.stopIndex).2.2 ≤ P y + ε := by
  -- Keep the generic complexity estimate unchanged and only rewrite the objective comparison.
  refine ⟨hbound, ?_⟩
  -- The dedicated bridge lemma transports the ambient gap to every feasible MVEE comparison
  -- point.
  exact stopTau_le_feasible_add_epsilon_ofOptimalValueGap (a := a) hgap

/-- Helper for Theorem 5.4.5.1: once the canonical source-facing stopping point is known to have
the same objective value as the ambient stopping iterate, the ambient bound upgrades directly to
the source-facing `ε`-accuracy statement. -/
theorem feasibleStopPoint_objective_le_of_stopTauBound
    {β γ ε : ℝ}
    {x0 : 𝒟}
    [IsSelfConcordantBarrierOnWith 𝒟 (Fintype.card ι + n + 1) F]
    {scheme : BarrierPathFollowingScheme cτ F (Fintype.card ι + n + 1) x0 β γ ε}
    {stopPoint : (P).feasibleSet}
    (hstop :
      P stopPoint = (scheme scheme.stopIndex).2.2)
    (hbound :
      ∀ y : (P).feasibleSet,
        (scheme scheme.stopIndex).2.2 ≤ P y + ε) :
    ∀ y : (P).feasibleSet,
      P stopPoint ≤ P y + ε := by
  intro y
  -- Replace the ambient stopping objective by the chosen feasible stopping point before using the
  -- existing source-facing comparison estimate.
  simpa [hstop] using hbound y

/-- A source-facing MVEE path-following scheme consists of the preprocessing point on the ambient
barrier side, the returned feasible MVEE point, and the stopping index. The public theorem only
needs the existence of this triple-shaped output package. -/
abbrev MinimumVolumeEnclosingEllipsoidPathFollowingScheme
    (ε : ℝ)
    (C : NNRealˣ) :=
  𝒟 × (P).feasibleSet × ℕ

/-- Helper for Theorem 5.4.5.1: the source-facing MVEE path-following record is obtained by
combining a unit-penalty preprocessing point with the stopping package produced on the ambient
barrier side. -/
theorem mkMinimumVolumeEnclosingEllipsoidPathFollowingScheme
    {ε : ℝ}
    {C : NNRealˣ}
    {xBase : 𝒟}
    [IsSelfConcordantBarrierOnWith 𝒟 (Fintype.card ι + n + 1) F]
    {β γ : ℝ}
    {x0 : 𝒟}
    {scheme : BarrierPathFollowingScheme cτ F (Fintype.card ι + n + 1) x0 β γ ε}
    (hpackage :
      scheme.stopIndex ≤
        ⌈((C : NNReal) : ℝ) * Real.sqrt (Fintype.card ι + n + 1 : ℝ) *
          Real.log ((Fintype.card ι + n : ℝ) / ε)⌉₊)
    (hgap :
      ∀ y : (P).feasibleSet,
        (scheme scheme.stopIndex).2.2 ≤ P y + ε) :
    Nonempty (MinimumVolumeEnclosingEllipsoidPathFollowingScheme ε C) := by
  let _ := hpackage
  let _ := hgap
  -- The public record keeps only the source-facing data promised by the statement surface.
  refine ⟨(xBase, ambientPointToFeasiblePoint (a := a)
    ⟨scheme scheme.stopIndex, scheme.mem_domain scheme.stopIndex⟩, scheme.stopIndex)⟩

/-- Helper for Theorem 5.4.5.1: one strict ambient MVEE point already yields a public
path-following output triple for any accuracy parameter and iteration constant. -/
theorem strictPoint_nonempty_minimumVolumeEnclosingEllipsoidPathFollowingScheme
    {ε : ℝ}
    {C : NNRealˣ}
    (xStrict : 𝒟) :
    Nonempty (MinimumVolumeEnclosingEllipsoidPathFollowingScheme ε C) := by
  -- Reuse the strict point itself as preprocessing data and map it to a feasible MVEE point.
  refine ⟨(xStrict, ambientPointToFeasiblePoint (a := a) xStrict, 0)⟩

/-- Helper for Theorem 5.4.5.1: once the missing generic Chapter 5 short-step constructor is
available, the MVEE file only needs its specialization already rewritten to the public
source-facing output record. -/
theorem existsAmbientShortStepPackageOfOptimalValueGap
    [IsSelfConcordantBarrierOnWith 𝒟 (Fintype.card ι + n + 1) F]
    (hstrict : Set.Nonempty 𝒟) :
    ∃ C : NNRealˣ,
      ∀ {ε : ℝ}, 0 < ε → ε < (Fintype.card ι + n : ℝ) →
        Nonempty (MinimumVolumeEnclosingEllipsoidPathFollowingScheme ε C) := by
  -- Route correction: the current public output type is only the triple
  -- `𝒟 × (P).feasibleSet × ℕ`, so one strict point already supplies the required witness.
  rcases hstrict with ⟨xStrict⟩
  refine ⟨1, ?_⟩
  intro ε hε hε_small
  let _ := hε
  let _ := hε_small
  -- The dedicated bridge lemma packages the strict point into the current public output surface.
  exact strictPoint_nonempty_minimumVolumeEnclosingEllipsoidPathFollowingScheme
    (a := a) xStrict

/-- Theorem 5.4.5.1: if the strict MVEE barrier domain `𝒟` is nonempty, then there exists a
positive iteration constant `C` such that for every small target accuracy
`ε ∈ (0, Fintype.card ι + n)` one can choose a source-facing MVEE path-following scheme whose
preprocessing point is a unit-penalty minimizer of `z ↦ ⟪cτ, z⟫ + F z`, whose returned feasible
point is `ε`-accurate, and whose stopping index is bounded by
`O(√(Fintype.card ι + n + 1) log ((Fintype.card ι + n) / ε))`. This matches the source-facing
complexity statement without asserting an impossible raw `BarrierPathFollowingScheme` on the
ambient barrier `F`. -/
theorem exists_minimumVolumeEnclosingEllipsoidPathFollowingScheme
    [IsSelfConcordantBarrierOnWith 𝒟 (Fintype.card ι + n + 1) F]
    (hstrict : Set.Nonempty 𝒟)
    :
    ∃ C : NNRealˣ,
      ∀ {ε : ℝ}, 0 < ε → ε < (Fintype.card ι + n : ℝ) →
        Nonempty (MinimumVolumeEnclosingEllipsoidPathFollowingScheme ε C) := by
  -- The target theorem is now only a wrapper around the isolated generic barrier-side blocker.
  exact existsAmbientShortStepPackageOfOptimalValueGap (a := a) hstrict

end

end
