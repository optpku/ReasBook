/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_19

-- Declarations for this item will be appended below by the statement pipeline.

section

/- Definition 12.11 is a `bridge/view` recall: it introduces no new owner beyond the chapter's
source-facing one-dimensional total-variation denoising objective.

Domain sampling against the nearby chapter/project owners gives the following split:

- `source-facing`: `one_dimensional_total_variation_denoising_objective`,
- `core/canonical`: `denoising_problem_objective`,
- `derived API`: `one_dimensional_total_variation_denoising_objective_apply`.

Primitive data are only the datum `d`, the canonical one-dimensional TV operator, and the positive
regularization parameter `λ : PosReal`, all already packaged by the source-facing owner in
Definition 12.19. This file should therefore recall that owner directly rather than rebuild a
lower-level specialization with a widened bare-real parameter. -/
recall one_dimensional_total_variation_denoising_objective
recall one_dimensional_total_variation_denoising_objective_apply

/- Definition 12.11 is exactly the existing chapter owner for one-dimensional TV denoising. -/
#check one_dimensional_total_variation_denoising_objective

/- Its pointwise formula is the corresponding existing apply theorem. -/
#check one_dimensional_total_variation_denoising_objective_apply

end
