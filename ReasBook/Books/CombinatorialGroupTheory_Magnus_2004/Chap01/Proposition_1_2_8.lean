/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 1-2-8: every finitely generated subgroup of a free group is itself free.

This source-facing item is a specialization of the canonical Nielsen-Schreier owner theorem
`subgroupIsFreeOfIsFree`; finite generation is not primitive data for the freeness conclusion, so
the file keeps a direct recall instead of a weaker local wrapper. -/
#check subgroupIsFreeOfIsFree
