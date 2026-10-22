/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory

/- Definition 2.1.2: a category is small when its objects form a set; in mathlib this is
the canonical abbreviation `SmallCategory`, expressing that the objects and morphisms live in
the same universe level. -/
recall SmallCategory (C : Type u) : Type (u + 1)
