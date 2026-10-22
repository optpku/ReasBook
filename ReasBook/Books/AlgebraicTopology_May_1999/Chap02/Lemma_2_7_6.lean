/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap02.Theorem_2_7_5

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 2.7.6 is the finite-cover specialization of the canonical group-level van Kampen theorem
from Theorem 2.7.5. The owner of the open-cover diagram and its colimit statement is therefore
`fundamental_group_is_colimit_of_path_connected_open_cover`, not a separate finite-cover copy. -/
#check fundamental_group_is_colimit_of_path_connected_open_cover

/- The corresponding compatibility of the universal comparison morphism with the cocone legs is
likewise the companion theorem from Theorem 2.7.5. -/
#check fundamental_group_is_colimit_of_path_connected_open_cover_desc_fac
