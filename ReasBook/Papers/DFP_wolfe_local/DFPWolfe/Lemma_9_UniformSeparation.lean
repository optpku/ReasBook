/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointSeparation

/-!
# Lemma 9: uniform endpoint separation

Paper label: `lem:separation` in `main-new.tex`.

For a sufficiently small initial scale, one constant `c_* > 0` separates
each endpoint `xₖ` from all other endpoints and the limiting circle by at
least `c_* r(k)`. Here `r(k)` is the squared scale of the corresponding cycle.

The proof is in the imported `EndpointSeparation` module. This file checks
the existing declaration for paper navigation.
-/

#check DFP.TwoPhaseOrbit.slowCurveUniformEndpointSeparation
