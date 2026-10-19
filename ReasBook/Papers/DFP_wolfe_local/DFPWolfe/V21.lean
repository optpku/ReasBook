/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import DFPWolfe.V21.PolarData
public import DFPWolfe.V21.NormalizedMap
public import DFPWolfe.V21.LimitingTwoCycle

/-!
# v21 polar construction: verified foundations

This independent entry point exports the polar data in Section 3.1, the
normalized alternating map in Section 3.2, and the limiting two-cycle family
(`eq:polar-two-cycle`) of the October 9, 2026 v21 submission.

The restoring drift, invariant tube, geometric separation, cutoff interpolation,
and final v21 counterexample theorem are not proved by this entry point.
The earlier center-manifold proof remains available through `DFPWolfe`.
-/
