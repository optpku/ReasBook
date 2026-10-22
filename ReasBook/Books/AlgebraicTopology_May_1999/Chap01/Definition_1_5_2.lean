/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.5.2: the circle `S^1` is the unit circle in `ℂ`, represented in mathlib by
`Circle`; it is used with its multiplicative topological group structure and with chosen
basepoint `1`. -/
recall Circle : Type

/- Elements of `Circle` are complex numbers of norm `1`. -/
recall Circle.norm_coe (z : Circle) : ‖(z : ℂ)‖ = 1

/- The circle has its canonical multiplicative commutative group structure. -/
#check (inferInstance : CommGroup Circle)

/- The circle has its canonical topological group structure under multiplication. -/
#check (inferInstance : IsTopologicalGroup Circle)

/- The chosen basepoint on the circle is the unit complex number `1`. -/
#check (1 : Circle)
