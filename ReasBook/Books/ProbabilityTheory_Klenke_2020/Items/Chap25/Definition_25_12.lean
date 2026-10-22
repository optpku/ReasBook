/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_10

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace ProbabilityTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "Process" => NNReal → Ω → ℝ

/-
Definition 25.12 is `source-facing`: it introduces the textbook interval notation
`\int_s^t H_r \, dW_r` for the Brownian Itô integral attached to the already-fixed owner data from
Definition 25.10 and Theorem 25.11. The `core/canonical` owner remains the terminal map
`BrownianItoIntegral.toContinuousLinearMap` together with its derived process
`brownianItoIntegralTruncatedProcess`; the declaration below is only the `bridge/view` that turns
that owner API into interval-integral notation, including the endpoint `t = ∞`.
-/
namespace BrownianItoIntegral

/-- Definition 25.12: for a Brownian Itô integral owner `I^W(H)`, the interval integral
`\int_s^t H_r \, dW_r` is the canonical increment of the truncated Brownian Itô process when
`t < ∞`, and for `t = ∞` it is the terminal Brownian Itô integral minus the time-`s` value. -/
noncomputable def intervalIntegral
    {μ : Measure Ω} {ℱ : TimeFiltration} (W : Process)
    [hIto : BrownianItoIntegral μ ℱ W]
    (H : PredictableSimpleProcessL2Closure ℱ μ)
    (s : NNReal) (t : ENNReal) : Ω → ℝ :=
  if t = ∞ then
    hIto.toContinuousLinearMap H - brownianItoIntegralTruncatedProcess W H s
  else
    brownianItoIntegralTruncatedProcess W H t.toNNReal -
      brownianItoIntegralTruncatedProcess W H s

scoped syntax "∫[" term "] " term ".." term ", " term : term

scoped macro_rules
  | `(∫[$W] $s..$t, $H) =>
      `(ProbabilityTheory.BrownianItoIntegral.intervalIntegral $W $H $s $t)

section Interval

variable {μ : Measure Ω} {ℱ : TimeFiltration} {W : Process}

/-- For a finite right endpoint, the interval integral is the increment of the canonical Brownian
Itô process `brownianItoIntegralTruncatedProcess W H` between `s` and `t`. -/
@[simp] theorem intervalIntegral_coe
    [BrownianItoIntegral μ ℱ W]
    (H : PredictableSimpleProcessL2Closure ℱ μ)
    (s t : NNReal) :
    (∫[W] s..(t : ENNReal), H) =
      brownianItoIntegralTruncatedProcess W H t -
        brownianItoIntegralTruncatedProcess W H s :=
  rfl

/-- At the endpoint `t = ∞`, the interval integral is the terminal Brownian Itô integral minus the
time-`s` value of the canonical Brownian Itô process. -/
@[simp] theorem intervalIntegral_top
    [hIto : BrownianItoIntegral μ ℱ W]
    (H : PredictableSimpleProcessL2Closure ℱ μ)
    (s : NNReal) :
    (∫[W] s..∞, H) =
      hIto.toContinuousLinearMap H -
        brownianItoIntegralTruncatedProcess W H s :=
  rfl

end Interval
end BrownianItoIntegral

end ProbabilityTheory
