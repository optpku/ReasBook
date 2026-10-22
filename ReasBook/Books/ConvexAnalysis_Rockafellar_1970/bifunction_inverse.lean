/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib

section RockafellarShared

/-- The canonical inverse `F_*` of a bifunction `F`, obtained by swapping the arguments and
negating the value:

`(F_* x)(u) = -(F u)(x)`.

This is shared across the Chapter 7/8 developments so the repository has a single top-level API
for the inverse bifunction construction. -/
noncomputable def bifunctionInverse
    {U X : Type*} (F : U → X → EReal) : X → U → EReal :=
  fun x u => -F u x

end RockafellarShared
