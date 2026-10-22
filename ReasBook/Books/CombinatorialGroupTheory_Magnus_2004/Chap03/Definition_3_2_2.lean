/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

-- Layer triage:
-- `source-facing`: for a `1`-complex `C`, a path from `v` to `w` is a finite composable sequence
-- of oriented edges in `C`, together with the vertex-specific empty path and the inverse path
-- obtained by reversing edges.
-- `core/canonical`: `Quiver.Path` is mathlib's owner abstraction for finite composable edge
-- sequences, and it already carries the empty path and length API.
-- `bridge/view`: Definition `3-2-1` equips every `OneComplex` with the quiver structure and
-- involutive edge reversal needed to read the textbook notion directly as `Quiver.Path` and its
-- canonical reverse operation.
-- Domain sampling:
-- 1. `Quiver.Path` is the canonical owner for finite composable edge sequences.
-- 2. `Quiver.Path.nil` gives the empty path at each vertex.
-- 3. `Quiver.Path.length` is the canonical length function on paths.
-- 4. `Quiver.Path.reverse` is the canonical inverse-path operation once arrow reversal is
--    available through `Quiver.HasReverse`.
-- Primitive vs. derived:
-- the primitive owner is `Quiver.Path` itself; the empty path, length, and inverse path are
-- derived canonical API and should be recalled directly rather than repackaged by local wrappers.

variable (C : OneComplex.{u, v})

/- Definition 3-2-2: in a `1`-complex `C`, a path from `v` to `w` is a finite composable
sequence of oriented edges from `v` to `w`. This notion is already owned by `Quiver.Path` on the
quiver underlying `C`, so the file keeps only direct recalls of the canonical owner API. -/
#check (Quiver.Path : C → C → Type _)

/- The empty path at a vertex is the canonical constant `Quiver.Path.nil`. -/
#check Quiver.Path.nil

/- The length of a path is the canonical function `Quiver.Path.length`. -/
#check Quiver.Path.length

/- The textbook inverse of a path is the canonical reversal `Quiver.Path.reverse`. -/
#check Quiver.Path.reverse

/- Reversing a one-edge path gives the one-edge path of the reversed edge. -/
#check Quiver.Path.reverse_toPath
