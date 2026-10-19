module

public import DFPWolfe
public import DFPWolfe.V21

/-!
# A counterexample to global convergence of classical DFP under the standard
strong Wolfe conditions

This module is the ReasBook entry point for the DFP Wolfe counterexample
formalization. The independent `DFPWolfe.V21` entry point adds the verified
foundations of the v21 polar construction; it does not export a complete v21
counterexample proof. `DFPWolfe` exposes the complete paper-facing surface, including
the all-dimensional counterexample with sharp one-half Hölder Hessian regularity,
identity-initialized matrix `liminf` certificate, planar convergence under weak
and strong Wolfe conditions, and degeneration for general secant iterations.
-/

public section

end
