/-
Authors: Chenyi Li
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/BFGSMinimumQOrder_Liu_2026/README.md (formalization contributor).
-/

module

public import Book

/-!
# BFGS Minimum Q-Order

Stable public entry point for the Lean formalization of the order-one lower
boundary for nonterminating exact-line-search BFGS, together with its convex
Broyden extension.

The principal declarations are:

* `BFGS.exists_orderOneExample`
* `BFGS.IsTrajectory.one_le_order`
* `BFGS.IsOrderOneExample.existsBroydenTrajectory`
* `BFGS.IsOrderOneExample.broydenPoints_eq`
* `BFGS.IsOrderOneExample.broydenOrder_eq_one`
-/
