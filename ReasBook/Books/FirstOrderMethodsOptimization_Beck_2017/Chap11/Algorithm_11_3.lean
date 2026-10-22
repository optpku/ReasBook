/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_4

-- Declarations for this item will be appended below by the statement pipeline.

/- Algorithm 11.3 is `source-facing`: the textbook step `x + 𝒰[i](T_i(x) - x_i)` is not a new
owner, but the Chapter 11 one-block update `block_coordinate_update` specialized to the
replacement value `T_i(x)`. The reusable API here is therefore a thin bridge from the source
surface to that canonical owner, together with the coordinate formulas downstream files use. -/

noncomputable section

universe u v

section

variable {ι : Type u} {Ei : ι → Type v}
variable [∀ i, AddCommGroup (Ei i)]

/-- Algorithm 11.3's textbook one-block proximal-gradient step is exactly the canonical Chapter 11
one-block update with displacement `T_i(x) - x_i`. -/
theorem block_proximal_gradient_update_eq_add_block_embedding
    (T : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (x : (j : ι) → Ei j) (i : ι) :
    block_coordinate_update x i (T i x - x i) = x + 𝒰[i] (T i x - x i) :=
  rfl

/-- Algorithm 11.3: updating the selected block `i` by the displacement `T_i(x) - x_i` replaces
the `i`-th coordinate by `T_i(x)`. -/
@[simp] theorem block_proximal_gradient_update_apply_eq
    (T : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (x : (j : ι) → Ei j) (i : ι) :
    (x + 𝒰[i] (T i x - x i)) i = T i x := by
  calc
    (x + 𝒰[i] (T i x - x i)) i
      = block_coordinate_update x i (T i x - x i) i := by
          rw [← block_proximal_gradient_update_eq_add_block_embedding T x i]
    _ = x i + (T i x - x i) := by
          rw [block_coordinate_update_apply_same]
    _ = T i x := by
          simp [sub_eq_add_neg, add_left_comm]

/-- Away from the selected block, the one-block update `x + 𝒰[i](T_i(x) - x_i)` leaves the other
coordinates unchanged. -/
@[simp] theorem block_proximal_gradient_update_apply_ne
    (T : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (x : (j : ι) → Ei j) {i j : ι} (hji : j ≠ i) :
    (x + 𝒰[i] (T i x - x i)) j = x j := by
  calc
    (x + 𝒰[i] (T i x - x i)) j
      = block_coordinate_update x i (T i x - x i) j := by
          rw [← block_proximal_gradient_update_eq_add_block_embedding T x i]
    _ = x j := by
          rw [block_coordinate_update_apply_ne _ _ hji]

/-- Algorithm 11.3's textbook update is the `Function.update` that replaces the selected block by
`T_i(x)`. -/
theorem block_proximal_gradient_update_eq_update
    [DecidableEq ι]
    (T : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (x : (j : ι) → Ei j) (i : ι) :
    x + 𝒰[i] (T i x - x i) = Function.update x i (T i x) := by
  ext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [hj]

end
