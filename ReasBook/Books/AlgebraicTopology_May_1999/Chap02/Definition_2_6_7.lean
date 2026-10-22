/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

open CategoryTheory Limits

/- Definition 2.6.7: a category is cocomplete when it has all colimits, expressed by the
canonical abbreviation `HasColimits`. -/
recall HasColimits (C : Type u) [Category.{v} C] : Prop

/- Completeness is the dual notion, expressed by the canonical abbreviation `HasLimits`. -/
recall HasLimits (C : Type u) [Category.{v} C] : Prop
