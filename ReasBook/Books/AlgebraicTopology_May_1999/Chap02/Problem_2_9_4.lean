/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

open CategoryTheory Limits

/- Problem 2.9.4 (1): any category with all coproducts and coequalizers is cocomplete, as
expressed by the canonical theorem constructing all colimits from these two classes of colimits. -/
recall has_colimits_of_hasCoequalizers_and_coproducts {C : Type u} [Category.{v} C]
    [HasCoproducts.{v} C] [HasCoequalizers C] : HasColimits C

/- Problem 2.9.4 (2): by passage to opposite categories, the dual statement says that products and
equalizers imply completeness, as recorded by the canonical theorem constructing all limits from
these two classes of limits. -/
recall has_limits_of_hasEqualizers_and_products {C : Type u} [Category.{v} C]
    [HasProducts.{v} C] [HasEqualizers C] : HasLimits C
