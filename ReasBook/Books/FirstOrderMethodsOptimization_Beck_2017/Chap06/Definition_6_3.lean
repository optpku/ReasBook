/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

/- Definition 6.3 is `source-facing`: it introduces the vector soft-thresholding operator from the
text. Domain sampling in the thresholding/finite-product domain against the project owner
`soft_thresholding` from `Definition_6_2`, mathlib's canonical coordinatewise `WithLp.map`, the
canonical `PiLp` owner from `Mathlib/Analysis/Normed/Lp/PiLp`, and the Euclidean specialization
`EuclideanSpace ℝ ι` from `Mathlib/Analysis/InnerProductSpace/PiL2` shows the right layering:

- `source-facing`: the vector operator `T_[λ]`,
- `core/canonical`: the coordinatewise `PiLp 2` lift built from `WithLp.map`,
- `bridge/view`: the coordinate evaluation formula.

Thus the primitive data are only the scalar owner `𝒯[λ]` and the ambient finite `PiLp 2`
product `PiLp 2 (fun _ : ι ↦ α)`; when `α = ℝ` and `ι = Fin n`, this is the usual coordinate
model for the textbook operator on `ℝ^n`, and the low-level `.ofLp` presentation is derived
encoding data rather than public owner data. -/

section

variable {ι : Type u}
variable {α : Type v} [Ring α] [LinearOrder α]

local notation "E" => PiLp 2 (fun _ : ι ↦ α)

/-- Definition 6.3: the soft-thresholding operator is the coordinatewise lift of the scalar owner
`𝒯[λ]` from Definition 6.2 to the canonical finite `PiLp 2` product. For `α = ℝ` and
`ι = Fin n`, this recovers the textbook vector operator `T_λ` on `ℝ^n`. -/
def softThreshold (lam : α) : E → E :=
  WithLp.map 2 <| Pi.map fun _ ↦ 𝒯[lam]

@[inherit_doc] scoped[SoftThreshold] notation "T_[" l "]" => softThreshold l

open scoped SoftThreshold

-- Proof sketch: `T_[λ]` is defined by lifting the coordinatewise map
-- `Pi.map (fun _ ↦ 𝒯[λ])` through `WithLp.map`, so evaluation at `i` is definitional.
/-- Evaluating `T_[λ]` applies the scalar owner `𝒯[λ]` to the chosen coordinate. -/
@[simp] theorem softThreshold_apply (lam : α) (x : E) (i : ι) :
    T_[lam] x i = 𝒯[lam] (x i) := rfl

end
