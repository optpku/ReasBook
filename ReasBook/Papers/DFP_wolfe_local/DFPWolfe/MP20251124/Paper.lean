/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import DFPWolfe.MP20251124.Results
public import DFPWolfe.MP20251124.SingleStepLimit
public import DFPWolfe.MP20251124.FixedCycle
public import DFPWolfe.MP20251124.FixedRecurrence

/-!
# DFP counterexample — the 20251124 polar proof

The manuscript uses one counter for Theorems 1, 2 and 4, Lemmas 3 and 5–11,
Corollary 12 and Lemma 13. `Results` contains the general counterexample,
planar convergence, and the polar search criterion and uniqueness in Lemma 3.
`SingleStepLimit.singleStepLimitMatrix` gives Lemma 5 for arbitrary gradient
factors tending to one from the right in the scale parameter.

`FixedRecurrence` implements the equal-angle recurrence and its scaled form.
`FixedCycle` proves the fixed reference cycle, the restoring derivative and
the transverse contraction at the reference point. The uniform nonlinear
tube estimates, geometry and objective realization for this specific recurrence
are still needed for Theorem 4.
-/
