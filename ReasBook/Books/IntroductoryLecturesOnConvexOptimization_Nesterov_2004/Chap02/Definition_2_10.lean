/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Definition 2.10 lies in the Euclidean quadratic hard-instance domain.

Sampled owner-style declarations in this domain:
* `smoothLowerBoundFunction` in `Definition_2_11`
* `quadraticObjective` in `Definition_1_9_1`
* `EuclideanSpace.equiv` in mathlib for the canonical coordinate model of `EuclideanSpace`
* the project's private `prefixPoint` pattern in `Algorithm_3_1` and `Proposition_3_28`, where
  prefix restriction is kept internal via `WithLp.toLp`

Best owner abstraction:
* `smoothLowerBoundFunction`

Primitive data:
* the hard-instance parameters `L` and `k`

Derived API:
* the ambient hard instance `quadraticHardInstanceFamily`

Source/core/bridge triage:
* source-facing: `quadraticHardInstanceFamily L k`
* core/canonical: `smoothLowerBoundFunction L (Nat.succPNat k.1)`
* bridge/view: the internal restriction from `ℝⁿ` to the first `k.1 + 1` coordinates
-/

private def hardInstancePrefix (k : Fin n) (x : E) :
    EuclideanSpace ℝ (Fin (k.1 + 1)) :=
  (EuclideanSpace.equiv (Fin (k.1 + 1)) ℝ).symm
    (fun i ↦ x (Fin.castLE (Nat.succ_le_of_lt k.2) i))

/-- Definition 2.10: for fixed `L` and `k : Fin n`, the textbook hard instance with one-based
index `k.1 + 1 ∈ {1, ..., n}` is the quadratic objective on `ℝⁿ` obtained by applying
`smoothLowerBoundFunction L (Nat.succPNat k.1)` to the first `k.1 + 1` zero-based
coordinates. -/
def quadraticHardInstanceFamily (L : ℝ) (k : Fin n) : E → ℝ :=
  fun x ↦ smoothLowerBoundFunction L (Nat.succPNat k.1) (hardInstancePrefix k x)
