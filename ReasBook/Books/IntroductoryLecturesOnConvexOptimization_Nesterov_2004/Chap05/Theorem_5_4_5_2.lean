/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.ProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_5_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_5_7

-- Declarations for this item will be appended below by the statement pipeline.

namespace MaximumVolumeInscribedEllipsoid

noncomputable section

open Matrix
open Set Topology Filter
open scoped BigOperators RealSymmetricMatrixSpace

variable {m n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "SymmMat" => 𝕊^n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "TailSpace" => E × ℝ
local notation "InscribedAmbientSpace" => SymmMat × TailSpace

noncomputable local instance instLocalChap05_Theorem_5_4_5_21 : SeminormedAddCommGroup TailSpace :=
  WithLp.seminormedAddCommGroupToProd 2 E ℝ

noncomputable local instance instLocalChap05_Theorem_5_4_5_22 : NormedAddCommGroup TailSpace :=
  WithLp.normedAddCommGroupToProd 2 E ℝ

noncomputable local instance instLocalChap05_Theorem_5_4_5_23 : NormedSpace ℝ TailSpace :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 E ℝ

noncomputable local instance instInnerProductSpaceChap05_Theorem_5_4_5_21 : InnerProductSpace ℝ TailSpace where
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

noncomputable local instance instLocalChap05_Theorem_5_4_5_24 : CompleteSpace TailSpace := inferInstance

noncomputable local instance instLocalChap05_Theorem_5_4_5_25 : SeminormedAddCommGroup InscribedAmbientSpace :=
  WithLp.seminormedAddCommGroupToProd 2 SymmMat TailSpace

noncomputable local instance instLocalChap05_Theorem_5_4_5_26 : NormedAddCommGroup InscribedAmbientSpace :=
  WithLp.normedAddCommGroupToProd 2 SymmMat TailSpace

noncomputable local instance instLocalChap05_Theorem_5_4_5_27 : NormedSpace ℝ InscribedAmbientSpace :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 SymmMat TailSpace

noncomputable local instance instInnerProductSpaceChap05_Theorem_5_4_5_22 : InnerProductSpace ℝ InscribedAmbientSpace where
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

/- Theorem 5.4.5.2 lies in the maximum-volume-inscribed-ellipsoid / barrier path-following
domain.

Sampled owner-style declarations in this domain:
* `RealSymmetricMatrixSpace.frobeniusInner` and the induced Frobenius/submodule normed-space
  structure in `Chap05/Definition_5_4_4_2`, the chapter owner layer for the ambient geometry on
  `𝕊^n`;
* `optimizationProblem` in `Chap05/Definition_5_4_5_6`, the source-facing owner of the convex
  reformulation on `(G, v, τ)`;
* `logarithmicBarrierDomain`, `logarithmicBarrierAmbientDomain`, `logarithmicBarrierAmbient`, and
  `logarithmicBarrier` in `Chap05/Definition_5_4_5_7`, the source-facing strict-domain barrier
  API and its exported ambient bridge for the same variables;
* `logDetBarrierAmbient` in `Chap05/Definition_5_4_4_5`, the chapter bridge for the
  `-log det` contribution on ambient symmetric matrices;
* `BarrierPathFollowingScheme` in `Chap05/Definition_5_3_4_1`, the chapter owner for short-step
  path-following data.

Best owner abstraction:
* source-facing: the inscribed-ellipsoid optimization problem and barrier on strict-cone triples
  `(G, v, τ)`;
* core/canonical: the Chapter 5 Frobenius/submodule inner-product geometry on `𝕊^n`, together
  with `BarrierPathFollowingScheme`;
* bridge/view: the raw ambient `L²` product `𝕊^n × E × ℝ`, used only to host the objective
  direction and the self-concordant-barrier assumption.

Primitive data:
* the half-space data `a`, `b`;
* the owner feasible set and owner strict barrier domain from `Definition_5_4_5_6` and
  `Definition_5_4_5_7`.

Derived API:
* the path-following existence theorem, whose stopping iterate is bridged back to an owner
  feasible point of `optimizationProblem a b`.

This refinement reuses the exported ambient bridge from `Definition_5_4_5_7` rather than
recreating a private raw pullback inside the theorem file. The theorem therefore speaks directly
in the chapter’s public maximum-volume-inscribed-ellipsoid barrier vocabulary.
-/

section

variable (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)

local notation "𝒟" => logarithmicBarrierAmbientDomain a b
local notation "F" => logarithmicBarrierAmbient a b

local notation "cτ" => ((0 : SymmMat), (0 : E), (1 : ℝ))
local notation "P" => optimizationProblem a b

-- Proof sketch: rewrite each scalar as a multiple of `1` and pull those scalars through the real
-- inner product.
/-- Helper for Theorem 5.4.5.2: on `ℝ`, the real inner product is ordinary multiplication. -/
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

-- Proof sketch: under the local `WithLp` product inner product on `E × ℝ`, the unit vector in
-- the scalar direction extracts the final coordinate.
/-- Helper for Theorem 5.4.5.2: the ambient scalar direction on `E × ℝ` extracts the `ℝ`
coordinate under the local `WithLp` inner-product structure. -/
theorem inner_tailUnit_eq_snd
    (x : TailSpace) :
    inner ℝ (((0 : E), (1 : ℝ)) : TailSpace) x = x.2 := by
  -- Unfold the local `WithLp` inner product on `E × ℝ` and cancel the zero coordinate.
  rcases x with ⟨v, τ⟩
  change inner ℝ (0 : E) v + inner ℝ (1 : ℝ) τ = τ
  have hscalar : inner ℝ (1 : ℝ) τ = τ := by
    simpa using real_inner_eq_mul (1 : ℝ) τ
  simpa [hscalar]

-- Proof sketch: under the local `WithLp` product inner product on `𝕊^n × E × ℝ`, the ambient
-- objective direction `cτ` only keeps the final scalar coordinate.
/-- Helper for Theorem 5.4.5.2: the ambient objective direction `cτ` extracts the `τ`
coordinate under the local `WithLp` inner-product structure on `𝕊^n × E × ℝ`. -/
theorem inner_cτ_eq_tau
    (x : InscribedAmbientSpace) :
    inner ℝ cτ x = x.2.2 := by
  -- Unfold the nested product inner product and cancel the zero coordinates of `cτ`.
  rcases x with ⟨X, v, τ⟩
  change inner ℝ (0 : SymmMat) X + inner ℝ (((0 : E), (1 : ℝ)) : TailSpace) (v, τ) = τ
  simpa [inner_tailUnit_eq_snd ((v, τ) : TailSpace)]

-- Proof sketch: an ambient strict barrier point already records strict positivity of the shape
-- variable and strict slack inequalities. Forgetting strictness therefore canonically yields an
-- owner feasible point of `optimizationProblem a b`.
/-- The shape component of an ambient strict barrier point canonically lies in `𝕊ⁿ₊₊`. -/
theorem ambientPoint_shape_mem
    (x : 𝒟) :
    x.1.1 ∈ (𝕊^n₊₊ : Set SymmMat) := by
  exact ((mem_logarithmicBarrierAmbientDomain_iff a b x.1.1 x.1.2.1 x.1.2.2).1 x.2).1

/-- The strict shape component of an ambient strict barrier point, viewed in the owner carrier
`𝕊ⁿ₊₊`. -/
abbrev ambientPointShape
    (x : 𝒟) : 𝕊^n₊₊ :=
  ⟨x.1.1, ambientPoint_shape_mem a b x⟩

-- Proof sketch: strict ambient-domain membership gives `τ - logDetBarrierAmbient n G > 0` and
-- strict second-order-cone inequalities. Weakening `<` to `≤` and restricting `G` to the strict
-- cone produces feasible-set membership for `optimizationProblem a b`.
/-- Every ambient strict barrier point canonically determines a feasible point of the owner
optimization problem by forgetting the strict inequalities to their nonstrict feasible-set
counterparts. -/
theorem ambientPoint_mem_feasibleSet
    (x : 𝒟) :
    (ambientPointShape a b x, x.1.2.1, x.1.2.2) ∈ (optimizationProblem a b).feasibleSet := by
  rcases (mem_logarithmicBarrierAmbientDomain_iff a b x.1.1 x.1.2.1 x.1.2.2).1 x.2 with
    ⟨_, hτ, hslack⟩
  change (ambientPointShape a b x, x.1.2.1, x.1.2.2) ∈ feasibleSet a b
  rw [mem_feasibleSet_iff]
  constructor
  · have hτ' : -Real.log (((x.1.1 : SymmMat) : Mat).det) < x.1.2.2 := by
      have hτ'' : 0 < x.1.2.2 + Real.log (((x.1.1 : SymmMat) : Mat).det) := by
        simpa [logDetBarrierAmbient] using hτ
      linarith
    exact le_of_lt (by simpa [ambientPointShape, logDetBarrier, logDetBarrierAmbient] using hτ')
  · rw [inscribedEllipsoid_subset_innerLePolyhedron_iff]
    intro i
    simpa [ambientPointShape, StrictPositiveSemidefiniteCone.toMatrix_def] using le_of_lt (hslack i)

/-- The canonical feasible point of `optimizationProblem a b` attached to an ambient strict
barrier point. -/
def ambientPointToFeasiblePoint
    (x : 𝒟) : (optimizationProblem a b).feasibleSet :=
  ⟨(ambientPointShape a b x, x.1.2.1, x.1.2.2), ambientPoint_mem_feasibleSet a b x⟩

namespace BarrierPathFollowingScheme

/-- The canonical owner feasible point determined by the stopping iterate of the inscribed-
ellipsoid path-following scheme. -/
abbrev stopFeasiblePoint
    [IsSelfConcordantBarrierOnWith 𝒟 (2 * m + n + 1) F]
    {β γ ε : ℝ} {x0 : 𝒟}
    (scheme : BarrierPathFollowingScheme cτ F (2 * m + n + 1) x0 β γ ε) :
    (optimizationProblem a b).feasibleSet :=
  ambientPointToFeasiblePoint a b
    ⟨scheme scheme.stopIndex, scheme.mem_domain scheme.stopIndex⟩

end BarrierPathFollowingScheme

/-- Helper for Theorem 5.4.5.2: the ambient strict barrier domain `𝒟` is nonempty once the
unit ball lies in `innerLePolyhedron a b` and every normal `a i` is nonzero. -/
theorem strictAmbientDomainNonempty
    (ha_nonzero : ∀ i : Fin m, a i ≠ 0)
    (hunit : Metric.closedBall (0 : E) 1 ⊆ innerLePolyhedron a b) :
    Set.Nonempty 𝒟 := by
  let G0 : SymmMat := (1 / 2 : ℝ) • (1 : SymmMat)
  let x0 : InscribedAmbientSpace := (G0, (0 : E), 1 + logDetBarrierAmbient n G0)
  refine ⟨x0, ?_⟩
  rw [mem_logarithmicBarrierAmbientDomain_iff]
  constructor
  · -- The scaled identity matrix is strictly positive definite, hence lies in `𝕊ⁿ₊₊`.
    have hG0_posDef : (((G0 : SymmMat) : Mat)).PosDef := by
      dsimp [G0]
      simpa [Algebra.smul_def] using
        (Matrix.PosDef.one : (1 : Mat).PosDef).smul (show 0 < (1 / 2 : ℝ) by norm_num)
    exact mem_strictPositiveSemidefiniteCone_of_posDef hG0_posDef
  constructor
  · -- The `τ` coordinate was chosen to leave one unit of positive slack in the epigraph term.
    simp [x0, G0, logDetBarrierAmbient]
  · intro i
    have hnorm_pos : 0 < ‖a i‖ := norm_pos_iff.mpr (ha_nonzero i)
    have hball : (‖a i‖)⁻¹ • a i ∈ Metric.closedBall (0 : E) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      simp [norm_smul, abs_of_pos (inv_pos.mpr hnorm_pos), hnorm_pos.ne']
    have hpoly := (mem_innerLePolyhedron_iff a b).1 (hunit hball) i
    have hnorm_le : ‖a i‖ ≤ b i := by
      have hinner_eq : inner ℝ (a i) ((‖a i‖)⁻¹ • a i) = ‖a i‖ := by
        rw [inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp [hnorm_pos.ne']
      rw [hinner_eq] at hpoly
      exact hpoly
    have hhalf_lt : (1 / 2 : ℝ) * ‖a i‖ < b i := by
      have hlt : (1 / 2 : ℝ) * ‖a i‖ < ‖a i‖ := by
        nlinarith
      exact lt_of_lt_of_le hlt hnorm_le
    -- The scaled identity sends `a i` to `(1/2) • a i`, so its norm is strictly below `b i`.
    simpa [x0, G0, logDetBarrierAmbient, norm_smul] using hhalf_lt

-- Proof sketch: a feasible inequality bounds `‖G aᵢ‖` above by the affine slack
-- `bᵢ - ⟪aᵢ, v⟫`, while positive definiteness and `aᵢ ≠ 0` force `G aᵢ ≠ 0`, hence that slack
-- is strictly positive.
/-- Helper for Theorem 5.4.5.2: feasibility together with `a i ≠ 0` forces the affine slack
`b i - ⟪a i, v⟫` to be strictly positive at that index. -/
theorem slackRightHandSide_pos_of_mem_feasibleSet
    {G : 𝕊^n₊₊} {v : E} {τ : ℝ}
    (hfeas : (G, v, τ) ∈ (P).feasibleSet)
    {i : Fin m}
    (hai : a i ≠ 0) :
    0 < b i - inner ℝ (a i) v := by
  have hfeasFormula :
      -Real.log ((((G : SymmMat) : Mat)).det) ≤ τ ∧
        ∀ j : Fin m, ‖((((G : SymmMat) : Mat)).toEuclideanLin (a j))‖ ≤
          b j - inner ℝ (a j) v := by
    simpa using (mem_feasibleSet_iff_formula a b G v τ).1 hfeas
  have hquad_pos :
      0 < inner ℝ ((((G : SymmMat) : Mat)).toEuclideanLin (a i)) (a i) := by
    exact (matrix_posDef_iff_forall_inner_pos (G : SymmMat)).1
      (strictPositiveSemidefiniteCone_posDef G) (a i) hai
  have himage_ne :
      ((((G : SymmMat) : Mat)).toEuclideanLin (a i)) ≠ 0 := by
    intro hzero
    have hzero_inner :
        inner ℝ ((((G : SymmMat) : Mat)).toEuclideanLin (a i)) (a i) = 0 := by
      simp [hzero]
    linarith
  have hnorm_pos :
      0 < ‖((((G : SymmMat) : Mat)).toEuclideanLin (a i))‖ := by
    exact norm_pos_iff.mpr himage_ne
  exact lt_of_lt_of_le hnorm_pos (hfeasFormula.2 i)

-- Proof sketch: if `aᵢ ≠ 0`, use positive definiteness as above; if `aᵢ = 0`, strict ambient
-- feasibility already forces `bᵢ > 0`, so every feasible point has strictly positive slack at
-- that index as well.
/-- Helper for Theorem 5.4.5.2: strict ambient feasibility upgrades every feasible affine slack
`b i - ⟪a i, v⟫` to a strict inequality, even when `a i = 0`. -/
theorem slackRightHandSide_pos_of_mem_feasibleSet_of_strictAmbientDomainNonempty
    (hstrict : Set.Nonempty 𝒟)
    {G : 𝕊^n₊₊} {v : E} {τ : ℝ}
    (hfeas : (G, v, τ) ∈ (P).feasibleSet)
    (i : Fin m) :
    0 < b i - inner ℝ (a i) v := by
  by_cases hai : a i = 0
  · rcases hstrict with ⟨xStrict, hxStrict⟩
    have hstrict_i :
        ‖((xStrict.1 : Mat).toEuclideanLin (a i))‖ <
          b i - inner ℝ (a i) xStrict.2.1 := by
      exact ((mem_logarithmicBarrierAmbientDomain_iff
        a b xStrict.1 xStrict.2.1 xStrict.2.2).1 hxStrict).2.2 i
    have hb : 0 < b i := by
      simpa [hai] using hstrict_i
    simpa [hai] using hb
  · exact slackRightHandSide_pos_of_mem_feasibleSet a b hfeas hai

-- Proof sketch: scale only the shape variable by `1 - s` and offset the epigraph coordinate by
-- `-(n + 1) log (1 - s)`. Positive definiteness is preserved, the determinant rewrite leaves one
-- extra `-log (1 - s)` of slack, and the second-order constraints become strict because the
-- right-hand sides are already positive.
/-- Helper for Theorem 5.4.5.2: shrinking the shape variable of a feasible triple produces a
strict ambient barrier-domain point. -/
theorem scaledFeasiblePoint_mem_logarithmicBarrierAmbientDomain
    (hstrict : Set.Nonempty 𝒟)
    {G : 𝕊^n₊₊} {v : E} {τ s : ℝ}
    (hfeas : (G, v, τ) ∈ (P).feasibleSet)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    ((((1 - s) • (G : SymmMat)), v, τ - (n + 1 : ℝ) * Real.log (1 - s)) :
      InscribedAmbientSpace) ∈ 𝒟 := by
  have hfeasFormula :
      -Real.log ((((G : SymmMat) : Mat)).det) ≤ τ ∧
        ∀ i : Fin m, ‖((((G : SymmMat) : Mat)).toEuclideanLin (a i))‖ ≤
          b i - inner ℝ (a i) v := by
    simpa using (mem_feasibleSet_iff_formula a b G v τ).1 hfeas
  rw [mem_logarithmicBarrierAmbientDomain_iff]
  constructor
  · -- Positive scalar scaling preserves positive definiteness of the shape matrix.
    refine mem_strictPositiveSemidefiniteCone_of_posDef ?_
    simpa [Algebra.smul_def] using
      (strictPositiveSemidefiniteCone_posDef G).smul (sub_pos.mpr hs.2)
  constructor
  · -- The logarithmic correction leaves one extra `-log (1 - s)` of epigraph slack.
    have hdetG_pos : 0 < ((((G : SymmMat) : Mat)).det) := by
      simpa using (strictPositiveSemidefiniteCone_posDef G).det_pos
    have hlog_smul :
        Real.log
            ((((((1 - s) • (G : SymmMat)) : SymmMat) :
              Matrix (Fin n) (Fin n) ℝ)).det) =
          (n : ℝ) * Real.log (1 - s) + Real.log ((((G : SymmMat) : Mat)).det) := by
      rw [show ((((((1 - s) • (G : SymmMat)) : SymmMat) :
            Matrix (Fin n) (Fin n) ℝ)).det) =
          (1 - s) ^ n * ((((G : SymmMat) : Mat)).det) by
            simpa [Algebra.smul_def] using
              (Matrix.det_smul (((G : SymmMat) : Mat)) (1 - s))]
      rw [Real.log_mul
        (ne_of_gt (show 0 < (1 - s) ^ n by
          exact pow_pos (sub_pos.mpr hs.2) _))
        (ne_of_gt hdetG_pos)]
      rw [← Real.rpow_natCast]
      rw [Real.log_rpow (sub_pos.mpr hs.2)]
    have hbase : 0 ≤ τ + Real.log ((((G : SymmMat) : Mat)).det) := by
      linarith [hfeasFormula.1]
    have hlog_neg : Real.log (1 - s) < 0 := by
      have hs_pos : 0 < 1 - s := sub_pos.mpr hs.2
      have hs_lt_one : 1 - s < 1 := by
        linarith [hs.1]
      exact Real.log_neg hs_pos hs_lt_one
    have hepigraph_slack :
        0 < τ - (n + 1 : ℝ) * Real.log (1 - s) -
          logDetBarrierAmbient n ((1 - s) • (G : SymmMat)) := by
      rw [logDetBarrierAmbient_apply, hlog_smul]
      linarith
    exact hepigraph_slack
  · intro i
    have hs_pos : 0 < 1 - s := sub_pos.mpr hs.2
    have hs_lt_one : 1 - s < 1 := by
      linarith [hs.1]
    have hscaled_apply :
        ((((((1 - s) • (G : SymmMat)) : SymmMat) : Mat)).toEuclideanLin (a i)) =
          (1 - s) • ((((G : SymmMat) : Mat)).toEuclideanLin (a i)) := by
      simp [Matrix.toEuclideanLin_apply, Matrix.smul_mulVec]
    have hscaled_norm :
        ‖((((((1 - s) • (G : SymmMat)) : SymmMat) : Mat)).toEuclideanLin (a i))‖ =
          (1 - s) * ‖((((G : SymmMat) : Mat)).toEuclideanLin (a i))‖ := by
      calc
        ‖((((((1 - s) • (G : SymmMat)) : SymmMat) : Mat)).toEuclideanLin (a i))‖ =
            ‖(1 - s) • ((((G : SymmMat) : Mat)).toEuclideanLin (a i))‖ := by
              rw [hscaled_apply]
        _ = |1 - s| * ‖((((G : SymmMat) : Mat)).toEuclideanLin (a i))‖ := by
              rw [norm_smul, Real.norm_eq_abs]
        _ = (1 - s) * ‖((((G : SymmMat) : Mat)).toEuclideanLin (a i))‖ := by
              rw [abs_of_pos hs_pos]
    have hstrict_slack :
        ‖((((((1 - s) • (G : SymmMat)) : SymmMat) : Mat)).toEuclideanLin (a i))‖ <
          b i - inner ℝ (a i) v := by
      rw [hscaled_norm]
      have hrhs_pos :=
        slackRightHandSide_pos_of_mem_feasibleSet_of_strictAmbientDomainNonempty
          a b hstrict hfeas i
      have hmul_le :
          (1 - s) * ‖((((G : SymmMat) : Mat)).toEuclideanLin (a i))‖ ≤
            (1 - s) * (b i - inner ℝ (a i) v) := by
        exact mul_le_mul_of_nonneg_left (hfeasFormula.2 i) (le_of_lt hs_pos)
      have hmul_lt :
          (1 - s) * (b i - inner ℝ (a i) v) < b i - inner ℝ (a i) v := by
        exact (mul_lt_iff_lt_one_left hrhs_pos).2 hs_lt_one
      exact lt_of_le_of_lt hmul_le hmul_lt
    exact hstrict_slack

-- Proof sketch: shrink only the shape variable and compensate the epigraph coordinate by the
-- determinant scaling correction. This approaches a feasible boundary point from inside `𝒟`.
/-- Helper for Theorem 5.4.5.2: every feasible inscribed-ellipsoid triple lies in the closure of
the strict ambient barrier domain `𝒟`. -/
theorem mem_closure_barrierAmbientDomain_of_mem_feasibleSet
    (hstrict : Set.Nonempty 𝒟)
    (G : 𝕊^n₊₊) (v : E) (τ : ℝ)
    (hfeas : (G, v, τ) ∈ (P).feasibleSet) :
    ((((G : SymmMat), v, τ) : InscribedAmbientSpace)) ∈ closure 𝒟 := by
  let path : ℝ → InscribedAmbientSpace := fun s ↦
    ((((1 - s) • (G : SymmMat)), v, τ - (n + 1 : ℝ) * Real.log (1 - s)) :
      InscribedAmbientSpace)
  have hpath :
      Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 ((((G : SymmMat), v, τ) : InscribedAmbientSpace))) := by
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
        have hG : ContinuousAt (fun s : ℝ ↦ (1 - s) • (G : SymmMat)) 0 := by
          fun_prop
        have hτ : ContinuousAt (fun s : ℝ ↦ τ - (n + 1 : ℝ) * Real.log (1 - s)) 0 := by
          exact continuousAt_const.sub (continuousAt_const.mul hlog)
        have htail : ContinuousAt (fun s : ℝ ↦ (v, τ - (n + 1 : ℝ) * Real.log (1 - s))) 0 := by
          exact continuousAt_const.prodMk hτ
        simpa [path] using hG.prodMk htail
      exact hpathCont.tendsto
    simpa [path] using
      (hpath0.mono_left nhdsWithin_le_nhds :
        Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 (path 0)))
  have hpath_mem : ∀ᶠ s in 𝓝[>] (0 : ℝ), path s ∈ 𝒟 := by
    have hIoo : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 :=
      Ioo_mem_nhdsGT zero_lt_one
    filter_upwards [hIoo] with s hs
    -- Each positive-time point on the path is strictly feasible in the ambient barrier domain.
    exact scaledFeasiblePoint_mem_logarithmicBarrierAmbientDomain
      a b hstrict hfeas hs
  -- The strict interior path approaches the feasible boundary point from inside `𝒟`.
  exact mem_closure_of_tendsto hpath hpath_mem

/-- Helper for Theorem 5.4.5.2: every feasible inscribed-ellipsoid triple canonically determines
a point of `closure 𝒟` in the ambient path-following space. -/
def feasiblePointClosure
    (hstrict : Set.Nonempty 𝒟)
    (y : 𝕊^n₊₊ × E × ℝ)
    (hy : y ∈ (P).feasibleSet) :
    closure 𝒟 :=
  ⟨(((y.1 : SymmMat), y.2.1, y.2.2) : InscribedAmbientSpace),
    mem_closure_barrierAmbientDomain_of_mem_feasibleSet
      a b hstrict y.1 y.2.1 y.2.2 hy⟩

/-- Helper for Theorem 5.4.5.2: evaluating `⟪cτ, ·⟫` on the canonical closure point attached to
a feasible inscribed-ellipsoid triple recovers the source-facing objective value `τ`. -/
theorem inner_cτ_feasiblePointClosure_eq_objective
    (hstrict : Set.Nonempty 𝒟)
    (y : 𝕊^n₊₊ × E × ℝ)
    (hy : y ∈ (P).feasibleSet) :
    inner ℝ cτ ((feasiblePointClosure a b hstrict y hy : closure 𝒟) :
      InscribedAmbientSpace) = P y := by
  -- The closure wrapper leaves the ambient coordinates unchanged, so the `cτ` rewrite and the
  -- owner objective formula apply verbatim.
  rcases y with ⟨G, v, τ⟩
  simp [feasiblePointClosure, inner_cτ_eq_tau, optimizationProblem_objective_apply]

/-- Helper for Theorem 5.4.5.2: any generic ambient `cτ`-objective gap estimate implies the
source-facing inscribed-ellipsoid stopping bound against every feasible comparison point. -/
theorem stopTau_le_feasible_add_epsilon_of_genericGap
    (hstrict : Set.Nonempty 𝒟)
    {β γ ε : ℝ}
    {x0 : 𝒟}
    [IsSelfConcordantBarrierOnWith 𝒟 (2 * m + n + 1) F]
    {scheme : BarrierPathFollowingScheme cτ F (2 * m + n + 1) x0 β γ ε}
    {xOpt : closure 𝒟}
    (hopt :
      ∀ z : closure 𝒟,
        inner ℝ cτ (xOpt : InscribedAmbientSpace) ≤ inner ℝ cτ (z : InscribedAmbientSpace))
    (hgap :
      inner ℝ cτ (scheme scheme.stopIndex) - inner ℝ cτ (xOpt : InscribedAmbientSpace) ≤ ε) :
    ∀ y ∈ (P).feasibleSet,
      P (BarrierPathFollowingScheme.stopFeasiblePoint a b scheme) ≤ P y + ε := by
  intro y hy
  let yClosure : closure 𝒟 := feasiblePointClosure a b hstrict y hy
  -- Compare the stopping iterate with the feasible point after transporting it to `closure 𝒟`.
  have hyOpt :
      inner ℝ cτ (xOpt : InscribedAmbientSpace) ≤
        inner ℝ cτ (yClosure : InscribedAmbientSpace) :=
    hopt yClosure
  have hyGap :
      inner ℝ cτ (scheme scheme.stopIndex) ≤
        inner ℝ cτ (yClosure : InscribedAmbientSpace) + ε := by
    linarith
  simpa [BarrierPathFollowingScheme.stopFeasiblePoint, ambientPointToFeasiblePoint, yClosure,
    inner_cτ_eq_tau, inner_cτ_feasiblePointClosure_eq_objective a b hstrict y hy,
    optimizationProblem_objective_apply] using hyGap

/-- Helper for Theorem 5.4.5.2: once a generic ambient short-step package supplies a stopping
bound and an ambient `cτ`-objective gap, the source-facing inscribed-ellipsoid conclusion follows
immediately. -/
theorem instantiateMviePathFollowingPackage
    (hstrict : Set.Nonempty 𝒟)
    {β γ ε : ℝ}
    {C : NNReal}
    {x0 : 𝒟}
    [IsSelfConcordantBarrierOnWith 𝒟 (2 * m + n + 1) F]
    {scheme : BarrierPathFollowingScheme cτ F (2 * m + n + 1) x0 β γ ε}
    {xOpt : closure 𝒟}
    (hbound :
      scheme.stopIndex ≤
        ⌈(C : ℝ) * Real.sqrt (2 * m + n + 1 : ℝ) *
          Real.log ((m + n : ℝ) / ε)⌉₊)
    (hopt :
      ∀ z : closure 𝒟,
        inner ℝ cτ (xOpt : InscribedAmbientSpace) ≤ inner ℝ cτ (z : InscribedAmbientSpace))
    (hgap :
      inner ℝ cτ (scheme scheme.stopIndex) - inner ℝ cτ (xOpt : InscribedAmbientSpace) ≤ ε) :
    scheme.stopIndex ≤
        ⌈(C : ℝ) * Real.sqrt (2 * m + n + 1 : ℝ) *
          Real.log ((m + n : ℝ) / ε)⌉₊ ∧
      ∀ y ∈ (P).feasibleSet,
        P (BarrierPathFollowingScheme.stopFeasiblePoint a b scheme) ≤ P y + ε := by
  -- Keep the generic complexity estimate unchanged and only rewrite the objective comparison.
  refine ⟨hbound, ?_⟩
  -- The dedicated bridge lemma transports the ambient gap to every feasible comparison point.
  exact stopTau_le_feasible_add_epsilon_of_genericGap a b hstrict hopt hgap

-- Proof sketch: specialize the standard short-step path-following existence theory to the
-- exported ambient bridge `F` on `𝒟` from `Definition_5_4_5_7`, then bridge the stopping
-- iterate to the canonical owner feasible point
-- `BarrierPathFollowingScheme.stopFeasiblePoint a b scheme` of the optimization problem from
-- `Definition_5_4_5_6`. The private barrier-side helper below still uses nonemptiness of the
-- strict ambient barrier domain `𝒟`; the final source-facing theorem later restates the textbook
-- interior hypothesis on `(optimizationProblem a b).feasibleSet` and also carries the
-- bounded-below premise already required by the source-facing `ε`-accuracy conclusion. The
-- logarithmic size term additionally needs `m + n > 0`. The iteration constant `C` is chosen
-- uniformly, before the accuracy parameter `ε`.

-- Semantic recall note: `lean_leansearch` did not surface a reusable Chapter 5 owner theorem for
-- this exact barrier, so the barrier-parameter fact is exposed here as the canonical local
-- companion instance rather than as an explicit assumption on the main source-facing theorem.
instance logarithmicBarrierAmbient.instIsSelfConcordantBarrierOnWith :
    IsSelfConcordantBarrierOnWith 𝒟 (2 * m + n + 1) F := by
  -- TODO: prove the canonical ambient barrier instance by decomposing `F` into the log-det
  -- epigraph barrier plus the finite sum of Lorentz slack barriers, then combine those two
  -- ingredients with the Chapter 5 barrier-sum and affine-pullback calculus.
  sorry

-- Proof sketch: the MVIE-specific closure transport is already complete, but the missing shared
-- Chapter 5 short-step package should be asked for directly at the final source-facing surface:
-- a scheme whose stopping point is feasible, `ε`-accurate, and satisfies the logarithmic bound.
/-- An auxiliary owner-style summary record for maximum-volume-inscribed-ellipsoid path-following
output, retaining only the returned feasible point of `optimizationProblem a b`, its
`ε`-accuracy, and the displayed logarithmic stopping bound. The main source-facing theorem below
returns this owner-style output package directly, while the raw ambient barrier-path-following
data remain in the private helper layer. -/
structure MaximumVolumeInscribedEllipsoidPathFollowingScheme
    (ε : ℝ)
    (C : NNRealˣ) where
  /-- The feasible point of `optimizationProblem a b` returned by the path-following method. -/
  stopPoint : (P).feasibleSet
  /-- The returned feasible point is `ε`-accurate against every feasible comparison point. -/
  optimality_gap :
    ∀ y ∈ (P).feasibleSet,
      P stopPoint ≤ P y + ε
  /-- The number of path-following iterations used to produce `stopPoint`. -/
  stopIndex : ℕ
  /-- The stopping index satisfies the displayed
  `O(√(2m + n + 1) log ((m + n) / ε))` bound. -/
  stopIndex_le :
    stopIndex ≤
      ⌈((C : NNReal) : ℝ) * Real.sqrt (2 * m + n + 1 : ℝ) *
        Real.log ((m + n : ℝ) / ε)⌉₊

/-- Helper for Theorem 5.4.5.2: the barrier-side short-step construction may still use the raw
ambient path-following data, but it is kept private and already stores the source-facing
feasible-point accuracy statement and stopping-index bound needed for the public record. -/
private structure AmbientShortStepScheme
    [IsSelfConcordantBarrierOnWith 𝒟 (2 * m + n + 1) F]
    (ε : ℝ) (C : NNRealˣ) where
  /-- The short-step centering parameter for the ambient scheme. -/
  β : ℝ
  /-- The short-step step-size parameter for the ambient scheme. -/
  γ : ℝ
  /-- The initial strict-domain point used by the raw ambient scheme. -/
  x0 : 𝒟
  /-- The private raw ambient path-following scheme. -/
  scheme : BarrierPathFollowingScheme cτ F (2 * m + n + 1) x0 β γ ε
  /-- The returned owner feasible point is `ε`-accurate against every feasible comparison point. -/
  optimality_gap :
    ∀ y ∈ (P).feasibleSet,
      P (BarrierPathFollowingScheme.stopFeasiblePoint a b scheme) ≤ P y + ε
  /-- The stopping index satisfies the displayed logarithmic bound. -/
  stopIndex_le :
    scheme.stopIndex ≤
      ⌈((C : NNReal) : ℝ) * Real.sqrt (2 * m + n + 1 : ℝ) *
        Real.log ((m + n : ℝ) / ε)⌉₊

/-- Helper for Theorem 5.4.5.2: a private ambient short-step scheme canonically determines the
public owner-style maximum-volume-inscribed-ellipsoid output record. -/
def AmbientShortStepScheme.toMaximumVolumeInscribedEllipsoidPathFollowingScheme
    [IsSelfConcordantBarrierOnWith 𝒟 (2 * m + n + 1) F]
    {ε : ℝ} {C : NNRealˣ}
    (scheme : AmbientShortStepScheme a b ε C) :
    MaximumVolumeInscribedEllipsoidPathFollowingScheme a b ε C where
  stopPoint := BarrierPathFollowingScheme.stopFeasiblePoint a b scheme.scheme
  optimality_gap := by
    intro y hy
    exact scheme.optimality_gap y hy
  stopIndex := scheme.scheme.stopIndex
  stopIndex_le := scheme.stopIndex_le

/-- Helper for Theorem 5.4.5.2: package the source-facing stopping claims attached to one actual
barrier path-following scheme. The public theorem below returns the owner-style output record, and
this proposition remains only as a local certificate for the private raw ambient scheme. -/
structure MaximumVolumeInscribedEllipsoidPathFollowingStopSpec
    [IsSelfConcordantBarrierOnWith 𝒟 (2 * m + n + 1) F]
    (β γ ε : ℝ)
    (x0 : 𝒟)
    (scheme : BarrierPathFollowingScheme cτ F (2 * m + n + 1) x0 β γ ε)
    (C : NNRealˣ) : Prop where
  /-- The canonical stopping feasible point is `ε`-accurate with respect to every feasible
  comparison point of the maximum-volume-inscribed-ellipsoid optimization problem. -/
  optimality_gap :
    ∀ y : (P).feasibleSet,
      P (BarrierPathFollowingScheme.stopFeasiblePoint a b scheme) ≤ P y + ε
  /-- The stopping index has the claimed path-following iteration bound. -/
  stopIndex_le :
    scheme.stopIndex ≤
      ⌈((C : NNReal) : ℝ) * Real.sqrt (2 * m + n + 1 : ℝ) *
        Real.log ((m + n : ℝ) / ε)⌉₊

/-- Helper for Theorem 5.4.5.2: once the generic Chapter 5 short-step existence scheme is
available, the MVIE file only needs its specialization already rewritten to the source-facing
feasible-point accuracy statement and stopping-index bound. -/
private theorem existsAmbientShortStepSchemeOfOptimalValueGap
    (hstrict : Set.Nonempty 𝒟)
    (hbounded : BddBelow (P '' ((P).feasibleSet : Set (𝕊^n₊₊ × E × ℝ))))
    (hmn_pos : 0 < (m + n : ℝ)) :
    ∃ C : NNRealˣ,
      ∀ {ε : ℝ}, 0 < ε → ε < (m + n : ℝ) →
        Nonempty (AmbientShortStepScheme a b ε C) := sorry

/-- Theorem 5.4.5.2 (Path-following complexity for problem (5.4.19)): if the feasible set of
`optimizationProblem a b` has nonempty interior, then there exists a positive iteration constant
`C`, uniform in `ε`, such that for every target accuracy `ε` with `0 < ε` there exists a
source-facing
maximum-volume-inscribed-ellipsoid path-following scheme whose returned feasible point is
`ε`-accurate and whose stopping index satisfies the displayed bound
`O(√(2m + n + 1) log ((m + n) / ε))`. -/
theorem exists_maximumVolumeInscribedEllipsoidPathFollowingScheme
    (hinterior :
      (interior ((P).feasibleSet : Set (𝕊^n₊₊ × E × ℝ))).Nonempty)
    :
    ∃ C : NNRealˣ,
      ∀ {ε : ℝ}, 0 < ε →
        Nonempty (MaximumVolumeInscribedEllipsoidPathFollowingScheme a b ε C) :=
  sorry

end

end

end MaximumVolumeInscribedEllipsoid
