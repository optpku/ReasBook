/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 3.13 is a recall-only item in the chapter's extended-valued subgradient /
subdifferential domain.

Primary domain:
- convex analysis of extended-real-valued functions on real inner-product spaces.

Relevant owner-style declarations sampled before refinement:
- `withTopEffectiveDomain`, the effective-domain owner from `Definition_3_3`;
- `IsSubgradientAt`, the primitive owner for affine lower-support inequalities on `dom f`;
- `subdifferential`, the unconstrained set-valued owner derived from `IsSubgradientAt`;
- `constrainedSubdifferential`, the constrained set-valued owner on a feasible set `Q`.

Best owner abstraction:
- source-facing: the textbook effective domain, subgradient, subdifferential, and constrained
  subdifferential of an extended-real-valued function;
- core/canonical: `withTopEffectiveDomain`, `IsSubgradientAt`, `subdifferential`, and
  `constrainedSubdifferential`;
- bridge/view: `mem_withTopEffectiveDomain_iff`, `mem_subdifferential_iff`, and
  `mem_constrainedSubdifferential_iff`.

Primitive data:
- an extended-real-valued function `f : V → WithTop ℝ`;
- a base point `x0`;
- a candidate vector `g`;
- optionally a feasible set `Q`.

Derived API:
- the effective-domain notation `dom f`;
- the unconstrained notation `∂ f(x0)`;
- the constrained notation `∂[Q] f(x0)`;
- the atomic membership expansions for these derived owners.

Source/core/bridge triage:
- source-facing: Definition 3.13 as stated in the textbook;
- core/canonical: the existing Chapter 3 owners above;
- bridge/view: the corresponding membership-expansion theorems.

The textbook states these notions on `ℝⁿ`, but the chapter owner already exposes the same
definitions on an arbitrary real inner-product space. This file therefore recalls that canonical
owner layer directly instead of introducing a Euclidean wrapper, a theorem-shaped alias, or a
parallel local notation shell. -/

/- The effective domain `dom f` is the set of points where the extended-real-valued function `f`
is finite. -/
recall withTopEffectiveDomain

/- A point belongs to `dom f` exactly when the value of `f` there is finite. -/
recall mem_withTopEffectiveDomain_iff

/- Definition 3.13: `IsSubgradientAt f x0 g` is the chapter's canonical predicate saying that `g`
is a subgradient of the extended-real-valued function `f` at `x0`; the corresponding
subdifferential `∂ f(x0)` and constrained subdifferential `∂[Q] f(x0)` are the derived sets of
all such supporting vectors. -/
recall IsSubgradientAt

/- The subdifferential `∂ f(x0)` is the set of all subgradients of `f` at `x0`. -/
recall subdifferential

/- Membership in the unconstrained subdifferential is exactly the owner predicate
`IsSubgradientAt f x0 g`. -/
recall mem_subdifferential_iff

/- The constrained subdifferential `∂[Q] f(x0)` consists of the vectors whose affine
lower-support inequality holds on the feasible set `Q`, with `x0 ∈ Q ∩ dom f`. -/
recall constrainedSubdifferential

/- Membership in the constrained subdifferential unfolds to feasibility of `x0` together with the
affine lower-support inequality on `Q`. -/
recall mem_constrainedSubdifferential_iff
