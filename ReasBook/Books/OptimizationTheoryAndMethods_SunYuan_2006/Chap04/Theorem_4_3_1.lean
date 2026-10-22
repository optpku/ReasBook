/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_19
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_7
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Algorithm_4_2_extra_1
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Filter.Extr
import Mathlib.Topology.Sequences

noncomputable section

open Filter

-- Domain sampling pass:
-- * primary domain: nonlinear conjugate-gradient runs on `ℝ^n` with exact line search;
-- * inspected chapter owners in this domain:
--   - `FletcherReevesMethod` from `Algorithm_4_2_extra_1` for the source-facing owner that
--     bundles the recurrence together with post-termination constancy;
--   - `FletcherReevesMethod.x_mem_lowerLevelSetOn_univ` from `Algorithm_4_2_extra_1` for the
--     exact-line-search lower-level-set invariance already attached to the source-facing owner;
--   - `FletcherReevesMethod.hasStationaryContinuation` from `Algorithm_4_2_extra_1` for the
--     owner-level bridge from the bundled post-termination field to the generic run API;
--   - `IsStationaryPoint` from `Chapter01.Definition_1_4_7` for the canonical stationary-point
--     owner that bundles vanishing gradient with differentiability.
--   - `Bornology.IsBounded.isCompact_closure` together with `IsCompact.tendsto_subseq` from
--     mathlib for the canonical bounded-sequence subsequence-extraction route in Euclidean space;
--   - `mem_closure_of_tendsto` together with `ContDiffOn.contDiffAt` from mathlib for the
--     set-neighborhood-to-pointwise-regularity bridge at an accumulation point
-- * best owner abstraction here: `ConjugateGradientRun` for primitive run data, with
--   `FletcherReevesMethod` as the source-facing exact-line-search owner and
--   `IsStationaryPoint` as the core stationary-point owner.
-- * source/core/bridge triage:
--   - `source-facing`: the numbered Fletcher-Reeves termination and accumulation-point results;
--   - `core/canonical`: `IsStationaryPoint`;
--   - `bridge/view`: the passage from `ContDiffOn` regularity on an open neighborhood of
--     `closure LevelSet` to the pointwise `ContDiffAt` input used by the stationary conclusion.
-- Primitive data vs derived API:
-- * primitive data: `x0`, `x`, `g`, `d`, `α`, and the `HasGradientAt` witnesses already owned
--   by `ConjugateGradientRun`;
-- * derived API here: the source-facing stationary and accumulation-point consequences that use
--   the owner-level lower-level-set invariance together with
--   `Bornology.IsBounded.isCompact_closure` and `IsCompact.tendsto_subseq`.

section

variable {n : ℕ}

local notation "Point" => ConjugateGradientPoint n
variable {f : Point → ℝ} (A : FletcherReevesMethod Point f)
local notation "LevelSet" => lowerLevelSetOn Set.univ f A.x0

/- Chapter04 Theorem 4.3.1 (1): if a Fletcher-Reeves sequence encoded as
`FletcherReevesMethod Point f` terminates at stage `k`, then the final point `A.x k`
is a stationary point of `f`. This is the exact owner theorem
`FletcherReevesMethod.isStationaryPoint_of_terminatedAt`, so the file stays at the
recall layer for clause (1) instead of keeping a parallel local wrapper. -/
#check fun (A : FletcherReevesMethod Point f) {k : ℕ} (hk : A.terminatedAt k) ↦
  (A.isStationaryPoint_of_terminatedAt hk : IsStationaryPoint f (A.x k))

/-- Chapter04 Theorem 4.3.1 (2): if the lower level set `LevelSet` is bounded, then the
Fletcher-Reeves iterate sequence has a limit point, expressed as a convergent subsequence of the
iterates. The post-termination constancy is already part of the source-facing owner
`FletcherReevesMethod Point f`. -/
theorem fletcherReeves_hasLimitPoint
    (hbounded : Bornology.IsBounded LevelSet) :
    ∃ xStar ∈ closure LevelSet, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (A.x ∘ φ) atTop (nhds xStar) := by
  exact hbounded.isCompact_closure.tendsto_subseq fun k ↦
      subset_closure (A.x_mem_lowerLevelSetOn_univ k)

/-- Primitive accumulation-point stationary conclusion: once a subsequential limit `xStar` of the
Fletcher-Reeves iterates is known to be a `C¹` point of `f`, the source stationary conclusion is
expressed canonically as `IsStationaryPoint f xStar`. The level-set `ContDiffOn` hypothesis from
Theorem 4.3.1 is handled separately by the bridge theorem below. -/
theorem fletcherReeves_limitPoint_stationary_of_contDiffAt
    (xStar : Point) (φ : ℕ → ℕ)
    (hC1At : ContDiffAt ℝ 1 f xStar)
    (hφ : StrictMono φ)
    (h_tendsto : Tendsto (A.x ∘ φ) atTop (nhds xStar)) :
    IsStationaryPoint f xStar := sorry

/-- Chapter04 Theorem 4.3.1 (3): if `f` is continuously differentiable on an open neighborhood
`U` containing the closure of the initial lower level set `LevelSet`, then every subsequential
limit `xStar` of the Fletcher-Reeves iterates is a stationary point of `f`. This is the
source-facing bridge from set-level regularity to the primitive pointwise `C¹` hypothesis used by
`fletcherReeves_limitPoint_stationary_of_contDiffAt`. -/
theorem fletcherReeves_limitPoint_stationary
    {U : Set Point}
    (hU_open : IsOpen U)
    (hLevelSetClosure_subset : closure LevelSet ⊆ U)
    (hC1 : ContDiffOn ℝ 1 f U)
    (xStar : Point) (φ : ℕ → ℕ)
    (hφ : StrictMono φ)
    (h_tendsto : Tendsto (A.x ∘ φ) atTop (nhds xStar)) :
    IsStationaryPoint f xStar := by
  have hxStar_mem_closure : xStar ∈ closure LevelSet := by
    exact mem_closure_of_tendsto h_tendsto <|
      Eventually.of_forall fun k ↦ A.x_mem_lowerLevelSetOn_univ (φ k)
  have hC1At : ContDiffAt ℝ 1 f xStar := by
    exact hC1.contDiffAt <| hU_open.mem_nhds (hLevelSetClosure_subset hxStar_mem_closure)
  exact fletcherReeves_limitPoint_stationary_of_contDiffAt A
    xStar φ hC1At hφ h_tendsto

end
