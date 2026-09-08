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
