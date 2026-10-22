/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u

variable {E : Type u}

section

variable [TopologicalSpace E] (g : E → EReal)

/- Definition 2.4: an extended-real-valued function is continuous over its domain exactly when it
is continuous on its effective domain in the canonical mathlib sense `ContinuousOn g
(effective_domain g)`. -/
#check (ContinuousOn g (effective_domain g))

end

section

variable [TopologicalSpace E] [FirstCountableTopology E] {g : E → EReal}

-- Proof sketch: rewrite `ContinuousOn g (effective_domain g)` as continuity of the restricted
-- map on the subtype `effective_domain g`, use `continuous_iff_seqContinuous`, then translate the
-- subtype convergence hypothesis back to ambient convergence with `tendsto_subtype_rng`.
/-- In a first-countable domain, continuity of an extended-real-valued function on its effective
domain is equivalent to preservation of limits of sequences valued in that domain. -/
theorem continuousOn_effective_domain_iff_subtype_seq_tendsto :
    ContinuousOn g (effective_domain g) ↔
      ∀ x : ℕ → effective_domain g, ∀ xstar : effective_domain g,
        Tendsto (fun n ↦ (x n : E)) atTop (𝓝 (xstar : E)) →
          Tendsto (fun n ↦ g (x n : E)) atTop (𝓝 (g (xstar : E))) := by
  rw [continuousOn_iff_continuous_restrict, continuous_iff_seqContinuous, SeqContinuous]
  constructor
  · intro hg x xstar hx
    simpa using hg ((tendsto_subtype_rng).2 hx)
  · intro hg x xstar hx
    simpa using hg x xstar ((tendsto_subtype_rng).1 hx)

end
