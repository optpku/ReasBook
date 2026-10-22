/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap12.Proposition_12_8.Duplication

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 12.8: for the diagonal duplication operator `𝒜(z) = (z, …, z)`, the FDPG
parameter from Algorithm 12.1 satisfies `L = ‖𝒜‖² / σ = p / σ`. -/
#check dual_block_duplication_fdpg_lipschitz_constant_eq
