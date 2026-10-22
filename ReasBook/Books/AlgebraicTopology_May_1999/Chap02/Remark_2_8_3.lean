/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap02.Theorem_2_7_5
import AlgebraicTopology_May_1999.Chap02.Proposition_2_8_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Remark 2.8.3: the compact-surface computation is a roadmap consequence rather than a single
new theorem. The formalized inputs are the group-level van Kampen theorem, the identification of
wedges with free products on fundamental groups, and the product formula for fundamental
groupoids; together with a separate computation of `π₁(ℝP²)`, these inputs compute the
fundamental group of any compact surface. -/
#check fundamental_group_is_colimit_of_path_connected_open_cover

/- The wedge-sum calculation supplies the free-product step used in the surface calculation. -/
#check wedge_fundamental_group_is_free_product

/- The product formula input is the canonical product isomorphism for fundamental groupoids. -/
#check FundamentalGroupoidFunctor.prodIso
