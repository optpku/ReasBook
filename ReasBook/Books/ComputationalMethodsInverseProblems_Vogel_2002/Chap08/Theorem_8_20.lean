/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_19
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_20.Minimizer
public import Mathlib.Topology.UniformSpace.UniformConvergence

public section

noncomputable section

/-!
Theorem 8.20. Statement-stage blocker.

The source theorem asserts stability of the constrained minimizers from
Theorem 8.19 under three kinds of perturbations: datum perturbations, operator
perturbations, and parameter perturbations.

In the current repository snapshot, `Book.Ch8.Theorem_8_19` intentionally
keeps the Chapter 8 objective `(8.73)` explicit as an unresolved parameter
instead of replacing it by a guessed TV/L² owner. The exact Lean meaning of
"stable" on this displayed theorem surface is likewise still unanchored in the
item payload, and the source-facing quantification over perturbed minimizers
has not yet been verified as either arbitrary minimizing selections or a
canonical uniquely determined family.

Replacing those missing anchors by concrete theorems of the form
`Filter.Tendsto ... (nhds fStar)` for a guessed owner would therefore drift
from the source semantics. This file remains a labeled check-only blocker
entry until the exact Chapter 8 stability surface is recovered.
-/

namespace VariationalRegularization

variable {d : ℕ}

/- Theorem 8.20. Main labeled source-facing blocker entry.

The exact Lean theorem surface for Theorem 8.20 still depends on three missing
anchors:
1. the verified owner of the Chapter 8 objective `(8.73)`,
2. the verified source-facing meaning of stability,
3. the verified quantification over perturbed minimizers in the datum,
   operator, and parameter clauses.

Accordingly, this target remains a labeled check-only blocker entry. It does
not export surrogate convergence theorems for a guessed TV-regularized least-
squares objective, nor does it fix a convergence codomain before the source
wording is anchored. Once those anchors are recovered, replace this blocker
with three atomic theorem clauses matching the datum, operator, and parameter
perturbation statements of the source.

Verified reusable anchors already present in the current repo snapshot:
-/

#check Filter.Tendsto
#check TendstoUniformlyOn
#check Set.ClosedConvex
#check ContinuousLinearMap.generalizedTikhonovFunctional
#check ContinuousLinearMap.IsTikhonovMinimizer
#check IsTvRegularizedMinimizer
#check IsUniqueTvRegularizedMinimizer
#check IsMinOn

end VariationalRegularization
