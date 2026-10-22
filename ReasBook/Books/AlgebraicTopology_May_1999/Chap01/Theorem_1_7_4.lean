/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 1.7.4 (1): the fundamental theorem of algebra says that every nonconstant complex
polynomial has a complex root; this is the canonical mathlib theorem `Complex.exists_root`,
which covers the textbook's monic normal form `x^n + c_1 x^(n - 1) + ... + c_n` with `n > 0`. -/
recall Complex.exists_root {f : Polynomial ℂ} (hf : 0 < f.degree) :
    ∃ z, f.IsRoot z

/- Theorem 1.7.4 (2): over `ℂ`, a complex polynomial has exactly `natDegree` many roots counted
with multiplicity; this is the canonical algebraically closed field root-count formula specialized
to `ℂ`. -/
#check (IsAlgClosed.card_roots_eq_natDegree : ∀ {p : Polynomial ℂ}, p.roots.card = p.natDegree)
