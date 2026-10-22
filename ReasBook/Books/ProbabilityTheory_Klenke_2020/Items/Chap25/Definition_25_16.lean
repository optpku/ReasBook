/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_67
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_9

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω}

local notation "TimeFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "Process" => NNReal → Ω → ℝ

/-- Definition 25.16: for a Brownian driver `W`, an integrand `H ∈ \mathcal E_{\mathrm{loc}}`,
and a candidate process `I`, the Brownian local Itô integral relation says that `I₀ = 0` and
that there exists a canonical Brownian Itô owner for `W` and an Itô localizing sequence `τₙ` for
`H`, recorded directly as a stopping-time approximation to `∞` together with cutoff integrands
`H^(τₙ)` in the canonical closure of the predictable step processes, along which the stopped
Brownian Itô integrals converge almost surely at each deterministic time to `I`. This keeps the
source-facing existence-based definition while reusing the chapter’s canonical Brownian-Itô owner
instead of exposing a free realization operator before Theorem 25.17 supplies existence and
uniqueness of a continuous realization. -/
@[mk_iff isBrownianLocalItoIntegralProcess_iff]
class IsBrownianLocalItoIntegralProcess
    (ℱ : TimeFiltration) (μ : Measure Ω) (W H I : Process) : Prop where
  /-- The integrand belongs to `\mathcal E_{\mathrm{loc}}`. -/
  locally_square_integrable : IsLocallySquareIntegrableProcess ℱ μ H
  /-- A Brownian local Itô integral starts from `0`. -/
  zero : I 0 = 0
  /-- Along some Itô localizing sequence for `H`, the canonical Brownian Itô processes of the
  cutoff integrands converge almost surely at each deterministic time to `I`. -/
  canonical_local_integral :
    ∃ hIto : BrownianItoIntegral μ ℱ W,
      ∃ τSeq : ℕ → Ω → ENNReal,
        IsStoppingTimeApproximationUpTo ℱ μ τSeq (fun _ ↦ ∞) ∧
          ∃ hτClosure : ∀ n : ℕ,
            MemPredictableStepProcessClosure ℱ μ
              (processBeforeStoppingTime H (τSeq n)),
            ∀ t : NNReal,
              ∀ᵐ ω ∂μ,
                Tendsto
                  (fun n ↦
                    hIto.toContinuousLinearMap
                      (PredictableSimpleProcessL2Closure.cutoffBefore t
                        (MemPredictableStepProcessClosure.toClosure
                          (hτClosure n))) ω)
                  atTop
                  (𝓝 (I t ω))

end ProbabilityTheory
