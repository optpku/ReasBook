/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Assumption_2_5.Region

public section

/- Assumption 2.5 (1): `Metric.cthickening` is the closed radius neighborhood
used by the source; mathlib defines it for every real radius. -/

/- Assumption 2.5 (2): the initial-potential threshold `Φ̄₁` combines the initial
objective value, regularity radius term, and multiplier-dependent corrections. -/

/- Assumption 2.5 (3): the exact-gradient objective threshold `Hdet` adds the
multiplier correction to the initial-potential threshold. -/

/- Assumption 2.5 (4): the closed `Δ`-neighborhood of the corresponding
objective--feasibility localization set is contained in the regularity region. -/

end
