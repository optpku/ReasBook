/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section12_part2

section RockafellarShared

/-- The canonical convex conjugate `f*`, defined as the Fenchel conjugate
`x* ↦ sup_x (⟪x, x*⟫ - f x)`. -/
noncomputable abbrev convexConjugate {n : ℕ} (f : (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  fenchelConjugate n f

end RockafellarShared
