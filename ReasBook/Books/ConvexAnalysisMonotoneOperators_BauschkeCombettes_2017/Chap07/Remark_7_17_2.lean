/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped InnerProductSpace

/- Remark 7.17.2 (1): every linear subspace `V` of a real Hilbert space is contained in its
double orthogonal complement `Vᗮᗮ`. -/
recall Submodule.le_orthogonal_orthogonal {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (K : Submodule 𝕜 E) : K ≤ Kᗮᗮ

/- Remark 7.17.2 (2): the triple orthogonal complement of a linear subspace `V` is its
orthogonal complement `Vᗮ`. -/
recall Submodule.triorthogonal_eq_orthogonal {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {K : Submodule 𝕜 E} : Kᗮᗮᗮ = Kᗮ

/- Remark 7.17.2 (3): taking the topological closure of a linear subspace `V` does not change its
orthogonal complement. -/
recall Submodule.orthogonal_closure {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (K : Submodule 𝕜 E) :
  K.topologicalClosureᗮ = Kᗮ
