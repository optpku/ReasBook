/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
/-!
Chapter12 Remark 12.8-extra-1

The source remark records two motivational facts about the reduced Hessian matrix method:
it is developed from the Lagrange-Newton method, and it uses only part of the Hessian matrix
of the Lagrangian function, thereby reducing per-iteration storage and computational cost.
-/

/-- The source remark records that the reduced Hessian matrix method was developed from the
Lagrange-Newton method. -/
inductive ReducedHessianMethodDevelopedFromLagrangeNewton : Prop where
  | intro

/-- The source remark records that the reduced Hessian matrix method uses only part of the
Hessian matrix of the Lagrangian function, thereby reducing per-iteration storage and
computational cost. -/
inductive ReducedHessianMethodUsesPartialLagrangianHessian : Prop where
  | intro

/-- The source remark records that the reduced Hessian matrix method is presented as developed
from the Lagrange-Newton method. -/
theorem reducedHessianMethod_developedFromLagrangeNewton :
    ReducedHessianMethodDevelopedFromLagrangeNewton :=
  .intro

/-- The source remark records that the reduced Hessian matrix method uses only part of the
Hessian matrix of the Lagrangian function, thereby reducing per-iteration storage and
computational cost. -/
theorem reducedHessianMethod_usesPartialLagrangianHessian :
    ReducedHessianMethodUsesPartialLagrangianHessian :=
  .intro

/-- Chapter12 Remark 12.8-extra-1: the reduced Hessian matrix method is developed from the
Lagrange-Newton method and uses only part of the Hessian matrix of the Lagrangian function,
thereby reducing per-iteration storage and computational cost. -/
theorem reducedHessianMethodIdea :
    ReducedHessianMethodDevelopedFromLagrangeNewton ∧
      ReducedHessianMethodUsesPartialLagrangianHessian := by
  exact ⟨reducedHessianMethod_developedFromLagrangeNewton,
    reducedHessianMethod_usesPartialLagrangianHessian⟩

#print axioms reducedHessianMethod_developedFromLagrangeNewton
#print axioms reducedHessianMethod_usesPartialLagrangianHessian
#print axioms reducedHessianMethodIdea
