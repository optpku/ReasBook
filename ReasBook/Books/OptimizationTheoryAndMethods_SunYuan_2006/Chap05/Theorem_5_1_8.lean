/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_4

noncomputable section

open Filter

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Source/core/bridge triage:
-- * source-facing: Theorem 5.1.8 is the convergence statement for the alternating rank-one
--   sequence `(5.1.55)` and its explicit limit `(5.1.56)`.
-- * core/canonical owner: `symmetrizedBroydenSequence_tendsto_limit`.
-- * bridge/view: none; this file is recall-only.
--
-- Domain sampling in the same Chapter 5 quasi-Newton matrix API:
-- * `dfpInverseUpdate` in `Algorithm_5_1_4` is the earlier owner for the DFP inverse update;
-- * `dfpInverseUpdate_eq_symmetricMatrixForm` in `Definition_5_1_extra_3` is the symmetric-matrix
--   bridge to that owner;
-- * `symmetrizedBroydenSequence` and `symmetrizedBroydenLimit` in
--   `Definition_5_1_extra_4` are the primitive data for the source sequence and its limit.
-- The public theorem surface here should therefore reuse the existing convergence owner directly
-- instead of introducing a parallel local theorem or wrapper.

/- Chapter05 Theorem 5.1.8: the alternating rank-one quasi-Newton sequence `(5.1.55)` converges
to the explicit matrix `(5.1.56)`, already owned upstream by
`symmetrizedBroydenSequence_tendsto_limit`. -/
#check
  fun (B : MatrixN) (s y c : Point) (hcs : dotProduct c s ≠ 0) ↦
    (symmetrizedBroydenSequence_tendsto_limit B s y c hcs :
      Tendsto (symmetrizedBroydenSequence B s y c) atTop
        (nhds (symmetrizedBroydenLimit B s y c)))
