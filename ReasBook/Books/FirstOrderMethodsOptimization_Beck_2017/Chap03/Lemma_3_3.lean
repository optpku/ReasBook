/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Lemma_3_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix

section

variable {m n p : ℕ}

local notation "PrimalSpace" => EuclideanSpace ℝ (Fin n)
local notation "IneqPerturbationSpace" => EuclideanSpace ℝ (Fin m)
local notation "EqPerturbationSpace" => EuclideanSpace ℝ (Fin p)

/- Lemma 3.3 is a `bridge/view` item in the perturbation-value-function API. The owner
declarations are `value_function` and the derived antitonicity theorem
`value_function_antitone_u` from `Lemma_3_4`, specialized to
`E = EuclideanSpace ℝ (Fin n)` and to the matrix linear map `A.toEuclideanLin`. The source writes
the affine constraint as `A *ᵥ x = b + t`, while the owner uses `A x + c = t`, so the faithful
specialization here is obtained by taking `c = -b`. -/
recall value_function
recall value_function_antitone_u

/-- Lemma 3.3: the perturbation value function is monotone with respect to relaxing the
coordinatewise inequality bounds, equivalently antitone in the bound parameter itself. In the
source convention `A *ᵥ x = b + t`, this is the specialization of the owner value function to the
offset `-b`. -/
theorem value_function_monotone
    (X : Set PrimalSpace) (f : PrimalSpace → EReal) (g : Fin m → PrimalSpace → EReal)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : EqPerturbationSpace)
    {u w : IneqPerturbationSpace} {t : EqPerturbationSpace}
    (huw : ∀ i : Fin m, u i ≤ w i) :
    value_function X f g A.toEuclideanLin (-b) (u, t) ≥
      value_function X f g A.toEuclideanLin (-b) (w, t) :=
  value_function_antitone_u X f g A.toEuclideanLin (-b) huw

end
