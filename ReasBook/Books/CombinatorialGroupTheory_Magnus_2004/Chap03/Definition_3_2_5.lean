/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Layer triage:
-- `source-facing`: in a `2`-complex `C`, paths are paths in the `1`-skeleton, with juxtaposition
-- as partially defined multiplication, vertexwise identity paths, and inverse path.
-- `core/canonical`: `Quiver.Path` is mathlib's owner abstraction for finite composable paths, with
-- `Quiver.Path.comp` for juxtaposition, `Quiver.Path.nil` for identity paths, and
-- `Quiver.Path.reverse` for inverse paths.
-- `bridge/view`: the textbook algebraic structure on `Π(C)` is exactly the standard quiver-path
-- API specialized to the quiver underlying the `1`-skeleton from Definitions `3-2-1` and `3-2-4`.
-- Domain sampling:
-- 1. `Quiver.Path.comp` is the canonical owner operation for concatenating composable paths.
-- 2. `Quiver.Path.comp_assoc` is the canonical associativity theorem for path juxtaposition.
-- 3. `Quiver.Path.nil_comp` and `Quiver.Path.comp_nil` are the canonical left and right identity
--    laws for the empty path at a vertex.
-- 4. `Quiver.Path.reverse` and `Quiver.Path.reverse_comp` are the canonical owner API for inverse
--    paths and the formula `(pq)⁻¹ = q⁻¹ p⁻¹`.
-- Primitive vs. derived:
-- this item contributes no new owner object beyond the canonical path-composition structure
-- already present on `Quiver.Path`, so the file should record direct recalls rather than
-- introducing a parallel local path package.

/- Definition 3-2-5: for a `2`-complex `C`, the set `Π(C)` of all paths in the `1`-skeleton
carries the canonical quiver-path multiplication by juxtaposition of composable paths.

This source-facing algebraic structure is exactly mathlib's path concatenation operation
`Quiver.Path.comp`, specialized to the quiver of the `1`-skeleton. -/
#check Quiver.Path.comp

/- Path juxtaposition is associative whenever the three paths are composable. -/
#check Quiver.Path.comp_assoc

/- The empty path at the initial vertex is a left identity for path juxtaposition. -/
#check Quiver.Path.nil_comp

/- The empty path at the terminal vertex is a right identity for path juxtaposition. -/
#check Quiver.Path.comp_nil

/- The inverse of a path is the canonical reversal of a quiver path. -/
#check Quiver.Path.reverse

/- The inverse of a product path is the product of the inverses in reverse order. -/
#check Quiver.Path.reverse_comp
