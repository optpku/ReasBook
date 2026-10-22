/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable (G : Type u) (X : Type v) [Group G] [TopologicalSpace X] [MulAction G X]

/- The source-facing orbit-space notation `X/H`, implemented as `X /[H]`, is the canonical orbit
quotient `MulAction.orbitRel.Quotient H X`. Equality of orbit classes is expressed by the
canonical theorem `MulAction.orbitRel.Quotient.mem_orbit`. -/
notation:70 X " /[" H "]" => MulAction.orbitRel.Quotient H X

/- Definition 3.8.7: for a group action from Definition 3.4.1, a `G`-space is the canonical
continuity condition `ContinuousConstSMul G X`; for a discrete topological group this says each
translate `x ↦ g • x` is continuous. -/
#check (ContinuousConstSMul G X)

/- In the orbit space `X /[G]`, the class of `x` lies in the orbit represented by `q` exactly when
`Quotient.mk'' x = q`. -/
#check (MulAction.orbitRel.Quotient.mem_orbit :
  ∀ {a : X} {q : X /[G]}, a ∈ q.orbit ↔ Quotient.mk'' a = q)
