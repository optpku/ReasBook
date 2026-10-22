/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Order.Filter.Extr
import Mathlib.Topology.MetricSpace.Lipschitz
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_7
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_19
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Algorithm_4_2_2

noncomputable section

open Filter

section

variable {n : ℕ}

local notation "Point" => ConjugateGradientPoint n
variable (f : Point → ℝ) (method : RestartFRConjugateGradientMethod n f)
local notation "LevelSet" => lowerLevelSetOn Set.univ f method.x0

-- Domain sampling pass:
-- * primary domain: restart Fletcher-Reeves / Crowder-Wolfe nonlinear conjugate-gradient
--   methods on `ℝ^n` with exact line search;
-- * inspected owner declarations in this domain:
--   - `RestartFRConjugateGradientMethod` from `Algorithm_4_2_2` for the source-facing
--     Crowder-Wolfe restart method data;
--   - `PeriodicRestartFRConjugateGradientMethod` from `Algorithm_4_2_2` for the reusable
--     period-`r` owner that specializes to the source threshold `r = n`;
--   - `RestartFRRestartStep` / `RestartFRContinueStep` from `Algorithm_4_2_2` for the
--     canonical restart-vs-continue branch data already attached to that owner;
--   - `lowerLevelSetOn` from `Chapter01.Theorem_1_3_19` for the canonical lower-level-set
--     owner used by nearby Chapter 4 convergence theorems.
-- * best owner abstraction here: the source-facing owner
--   `RestartFRConjugateGradientMethod n f`;
-- * layer targeted by the rewrite: `source-facing`, because Algorithm 4.2.2 already owns the
--   Crowder-Wolfe restart data and no extra wrapper is mathematically needed.
-- Primitive data vs derived API:
-- * primitive data: the initial point `x0`, restart states `method k`, exact line search,
--   iterate updates, gradients, and restart/continuation branch laws already owned by
--   `RestartFRConjugateGradientMethod`;
-- * derived API here: only the accumulation-point existence and stationarity conclusion under
--   bounded lower-level-set and local smoothness assumptions on that canonical owner.

/-- A stationary accumulation point of a restart Fletcher-Reeves / Crowder-Wolfe run is an
accumulation point of the iterate sequence `method.x` together with the canonical
stationary-point condition for `f`. -/
structure RestartFRConjugateGradientStationaryAccumulationPoint where
  point : Point
  subsequence : ℕ → ℕ
  strictMono_subsequence : StrictMono subsequence
  tendsto_subsequence : Tendsto (method.x ∘ subsequence) atTop (nhds point)
  stationary : IsStationaryPoint f point

namespace RestartFRConjugateGradientStationaryAccumulationPoint

/-- The chosen subsequence converges to the stationary accumulation point along the canonical
iterate projection `method.x`. -/
theorem tendsto_iterates
    (h : RestartFRConjugateGradientStationaryAccumulationPoint f method) :
    Tendsto (method.x ∘ h.subsequence) atTop (nhds h.point) :=
  h.tendsto_subsequence

/-- The stationary limit point of a restart Fletcher-Reeves / Crowder-Wolfe run has vanishing
gradient. -/
theorem gradient_eq_zero
    (h : RestartFRConjugateGradientStationaryAccumulationPoint f method) :
    gradient f h.point = 0 :=
  h.stationary.gradient_eq_zero

end RestartFRConjugateGradientStationaryAccumulationPoint

/-- Chapter04 Theorem 4.3.2 (stationary accumulation point for the Crowder-Wolfe
conjugate-gradient method): let `method` be the restart Fletcher-Reeves / Crowder-Wolfe method
from Algorithm 4.2.2. If the initial lower level set `LevelSet` is bounded, `f` is `C¹` on
that level set, and `gradient f` is Lipschitz there, then the iterate sequence `(method k).x`
has a convergent subsequence whose limit is stationary, packaged by
`RestartFRConjugateGradientStationaryAccumulationPoint f method`. -/
theorem crowderWolfeConjugateGradient_exists_stationaryAccumulationPoint
    (hLevelSetBounded : Bornology.IsBounded LevelSet)
    (hC1 : ContDiffOn ℝ 1 f LevelSet)
    (hGradLipschitz : ∃ L : NNReal, LipschitzOnWith L (gradient f) LevelSet) :
    Nonempty (RestartFRConjugateGradientStationaryAccumulationPoint f method) := sorry

#print axioms crowderWolfeConjugateGradient_exists_stationaryAccumulationPoint

end
