/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7

-- Declarations for this item will be appended below by the statement pipeline.

/- Text 6.3 is `bridge/view`: Definition 6.7 already owns the Moreau envelope `M[μ, f]`, Chapter 2
already owns `infimal_convolution` together with the textbook notation `□`, and Definition 6.7
also owns the quadratic kernel `ω_μ`. The source only recalls that `M_f^μ` is the infimal
convolution of `f` with `ω_μ`, so the canonical owner declarations are reused directly here
instead of keeping a duplicate theorem wrapper. -/

recall infimal_convolution
recall moreau_quadratic_kernel
recall moreau_envelope
