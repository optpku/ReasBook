/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.Topology.Instances.EReal.Lemmas

-- Declarations for this item will be appended below by the statement pipeline.

/-- Text 1.0.51: the extended real line `EReal = [-∞, +∞]`, equipped with its canonical order
topology, is compact. The textbook description by real intervals together with rays at `⊥` and
`⊤` describes this same topology. -/
theorem extendedReal_compactSpace : CompactSpace EReal := inferInstance
