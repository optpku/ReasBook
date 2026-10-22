/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap05.Proposition_5_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open WithLp (ofLp)

section

variable {n : ℕ}

local notation "Δ" => stdSimplex ℝ (Fin n)
local notation "E₁" => WithLp 1 (Fin n → ℝ)
local notation "Δ₁" => Set.preimage (ofLp : E₁ → Fin n → ℝ) Δ

/- Remark 5.18 is `source-facing`: the primitive object is the entropy-shifted simplex function
`x ↦ f(x) - α ‖x‖₁²`. Domain sampling points to the Chapter 4 entropy owner
`negative_entropy_on_stdSimplex` and Proposition 5.14's real-valued simplex bridge, together with
mathlib's canonical real-valued owner `ConvexOn` on the `WithLp 1` simplex model. The main labeled
entry is therefore a convexity statement on `Δ₁`, while the helper lemmas record the simplex-
specific identities `‖x‖₁ = 1` and `f(x) - α ‖x‖₁² = f(x) - α`. -/

-- Proof sketch: expand `hx : x ∈ Δ₁` as `ofLp x ∈ stdSimplex ℝ (Fin n)`, rewrite the
-- `WithLp 1` norm by the finite `ℓ₁` coordinate formula, then use nonnegativity of simplex
-- coordinates to
-- remove absolute values and the simplex equation `∑ i, ofLp x i = 1`.
/-- Every point of the unit simplex has `ℓ₁`-norm equal to `1` in the canonical `WithLp 1`
model. -/
@[simp] theorem l1_norm_eq_one_of_mem_stdSimplex {x : E₁} (hx : x ∈ Δ₁) :
    ‖x‖ = 1 := by
  -- Rewrite the `WithLp 1` norm in coordinates and use simplex nonnegativity to remove
  -- absolute values.
  rw [PiLp.norm_eq_of_L1]
  have hxΔ : ofLp x ∈ Δ := hx
  calc
    ∑ i : Fin n, ‖ofLp x i‖ = ∑ i : Fin n, |ofLp x i| := by
      simp [Real.norm_eq_abs]
    _ = ∑ i : Fin n, ofLp x i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [abs_of_nonneg]
      exact (mem_Icc_of_mem_stdSimplex hxΔ i).1
    _ = 1 := by
      simpa using hxΔ.2

/-- Every point of the unit simplex has squared `ℓ₁`-norm equal to `1` in the canonical
`WithLp 1` model. -/
@[simp] theorem l1_norm_sq_eq_one_of_mem_stdSimplex {x : E₁} (hx : x ∈ Δ₁) :
    ‖x‖ ^ (2 : ℕ) = 1 := by
  rw [l1_norm_eq_one_of_mem_stdSimplex hx]
  norm_num

-- Proof sketch: substitute `‖x‖ = 1` from `l1_norm_eq_one_of_mem_stdSimplex hx`, square this
-- identity, and simplify the scalar expression.
/-- On the unit simplex, subtracting `α ‖x‖₁²` from the negative entropy is the same as
subtracting the constant `α`. -/
@[simp] theorem negative_entropy_sub_alpha_l1Square_eq_sub_alpha_of_mem_stdSimplex
    (α : ℝ) {x : E₁} (hx : x ∈ Δ₁) :
    (negative_entropy_on_stdSimplex n (ofLp x)).toReal - α * ‖x‖ ^ (2 : ℕ) =
      (negative_entropy_on_stdSimplex n (ofLp x)).toReal - α := by
  -- The simplex normalization `‖x‖₁² = 1` turns the quadratic shift into the constant `α`.
  rw [l1_norm_sq_eq_one_of_mem_stdSimplex hx]
  ring

/-- On the unit simplex, the entropy shift `x ↦ f(x) - α ‖x‖₁²` agrees with the constant
translate `x ↦ f(x) - α`. -/
theorem negative_entropy_sub_alpha_l1Square_eqOn_sub_alpha_stdSimplex (α : ℝ) :
    Set.EqOn
      (fun x : E₁ ↦
        (negative_entropy_on_stdSimplex n (ofLp x)).toReal - α * ‖x‖ ^ (2 : ℕ))
      (fun x : E₁ ↦ (negative_entropy_on_stdSimplex n (ofLp x)).toReal - α)
      Δ₁ := by
  intro x hx
  simpa using negative_entropy_sub_alpha_l1Square_eq_sub_alpha_of_mem_stdSimplex α hx

-- Proof sketch: use Proposition 5.14 to get `1`-strong convexity of
-- `x ↦ (negative_entropy_on_stdSimplex n (ofLp x)).toReal` on `Δ₁`, lower the modulus to `0`,
-- obtain convexity, and then apply
-- `ConvexOn.add_const (-α)`. The companion `Set.EqOn` lemma above rewrites the source expression
-- to that constant translate on all points of `Δ₁`.
/-- Convexity consequence for Remark 5.18: the negative entropy on the unit simplex remains
convex after subtracting `α ‖x‖₁²`, since this term is constant on the simplex. In particular,
this holds for every `α > 0` as stated in the source. -/
theorem negative_entropy_sub_alpha_l1Square_convexOn_stdSimplex (α : ℝ) :
    ConvexOn ℝ Δ₁
      (fun x : E₁ ↦
        (negative_entropy_on_stdSimplex n (ofLp x)).toReal - α * ‖x‖ ^ (2 : ℕ)) := by
  -- Lower Proposition 5.14 from modulus `1` to modulus `0` to recover convexity of the entropy.
  have hbaseConvex :
      ConvexOn ℝ Δ₁
        (fun x : E₁ ↦ (negative_entropy_on_stdSimplex n (ofLp x)).toReal) := by
    simpa using
      (negative_entropy_on_stdSimplex_is_one_strongly_convex_l1 (n := n)).mono
        (show (0 : ℝ) ≤ 1 by norm_num)
  -- A constant vertical shift preserves convexity.
  have htranslated :
      ConvexOn ℝ Δ₁
        (fun x : E₁ ↦ (negative_entropy_on_stdSimplex n (ofLp x)).toReal - α) := by
    simpa [sub_eq_add_neg] using hbaseConvex.add_const (-α)
  -- Rewrite the source expression to that constant translate on the simplex.
  refine htranslated.congr ?_
  intro x hx
  symm
  exact negative_entropy_sub_alpha_l1Square_eq_sub_alpha_of_mem_stdSimplex (n := n) α hx

/-- Helper for Remark 5.18: the negative entropy of a simplex vertex is `0`. -/
lemma entropyValue_singleVertex (i : Fin n) :
    (negative_entropy_on_stdSimplex n (Pi.single i (1 : ℝ))).toReal = 0 := by
  -- Collapse the entropy sum to the unique nonzero coordinate of the simplex vertex.
  rw [negative_entropy_on_stdSimplex_toReal_of_mem (n := n) (single_mem_stdSimplex ℝ i)]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hij
    simp [Pi.single_eq_of_ne hij]
  · simp

/-- Helper for Remark 5.18: the midpoint of two distinct simplex vertices has value `1 / 2`
at each chosen vertex and vanishes elsewhere. -/
lemma twoVertexMidpoint_apply
    (i0 i1 : Fin n) (h01 : i0 ≠ i1) (i : Fin n) :
    (((1 / 2 : ℝ) • (PiLp.single 1 i0 (1 : ℝ) : E₁) +
        (1 / 2 : ℝ) • (PiLp.single 1 i1 (1 : ℝ) : E₁)) i) =
      if i = i0 ∨ i = i1 then (1 / 2 : ℝ) else 0 := by
  -- Split on whether the queried coordinate is one of the two active vertices.
  by_cases hi0 : i = i0
  · subst hi0
    simp [h01]
  · by_cases hi1 : i = i1
    · subst hi1
      simp [hi0]
    · simp [hi0, hi1]

/-- Helper for Remark 5.18: the difference of two distinct simplex vertices has coordinates
`1`, `-1`, and `0` on the three support cases. -/
lemma twoVertexDifference_apply
    (i0 i1 : Fin n) (h01 : i0 ≠ i1) (i : Fin n) :
    (((PiLp.single 1 i0 (1 : ℝ) : E₁) - (PiLp.single 1 i1 (1 : ℝ) : E₁)) i) =
      if i = i0 then 1 else if i = i1 then (-1 : ℝ) else 0 := by
  -- Split on the same support cases to expose the exact coordinate formula.
  by_cases hi0 : i = i0
  · subst hi0
    simp [h01]
  · by_cases hi1 : i = i1
    · subst hi1
      simp [hi0]
    · simp [hi0, hi1]

/-- Helper for Remark 5.18: the midpoint of two distinct simplex vertices has entropy
`- log 2`. -/
lemma entropyValue_twoVertexMidpoint
    (i0 i1 : Fin n) (h01 : i0 ≠ i1) :
    (negative_entropy_on_stdSimplex n
      (ofLp ((1 / 2 : ℝ) • (PiLp.single 1 i0 (1 : ℝ) : E₁) +
        (1 / 2 : ℝ) • (PiLp.single 1 i1 (1 : ℝ) : E₁)))).toReal = - Real.log 2 := by
  let m : E₁ :=
    (1 / 2 : ℝ) • (PiLp.single 1 i0 (1 : ℝ) : E₁) +
      (1 / 2 : ℝ) • (PiLp.single 1 i1 (1 : ℝ) : E₁)
  have hm : ofLp m ∈ Δ := by
    -- The midpoint stays in the simplex because the simplex is convex.
    simpa [m, WithLp.ofLp_add, WithLp.ofLp_smul] using
      (convex_stdSimplex (𝕜 := ℝ) (ι := Fin n))
        (single_mem_stdSimplex ℝ i0) (single_mem_stdSimplex ℝ i1)
        (by norm_num) (by norm_num) (by norm_num)
  rw [show
      (negative_entropy_on_stdSimplex n
        (ofLp ((1 / 2 : ℝ) • (PiLp.single 1 i0 (1 : ℝ) : E₁) +
          (1 / 2 : ℝ) • (PiLp.single 1 i1 (1 : ℝ) : E₁)))).toReal =
        (negative_entropy_on_stdSimplex n (ofLp m)).toReal by rfl]
  rw [negative_entropy_on_stdSimplex_toReal_of_mem (n := n) hm]
  -- Only the two distinguished coordinates contribute to the entropy sum.
  have hsplit :
      (∑ j : Fin n, m.ofLp j * Real.log (m.ofLp j)) =
        Finset.sum (Finset.univ.erase i0) (fun j ↦ m.ofLp j * Real.log (m.ofLp j)) +
          m.ofLp i0 * Real.log (m.ofLp i0) := by
    exact
      (Finset.sum_erase_add
        (s := Finset.univ) (a := i0)
        (f := fun j : Fin n ↦ m.ofLp j * Real.log (m.ofLp j))
        (Finset.mem_univ i0)).symm
  rw [hsplit]
  rw [Finset.sum_eq_single_of_mem i1]
  · have hi0 : m i0 = (1 / 2 : ℝ) := by
      simpa [m] using twoVertexMidpoint_apply (n := n) i0 i1 h01 i0
    have hi1 : m i1 = (1 / 2 : ℝ) := by
      dsimp [m]
      simp [h01]
    rw [hi0, hi1]
    have hlog : Real.log (1 / 2 : ℝ) = - Real.log 2 := by
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
    rw [hlog]
    ring
  · exact Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ i1⟩
  · intro j hj hjne
    have hj0 : j ≠ i0 := (Finset.mem_erase.mp hj).1
    have hj1 : j ≠ i1 := hjne
    have hj : m j = 0 := by
      have hcoord := twoVertexMidpoint_apply (n := n) i0 i1 h01 j
      rw [if_neg (by exact fun h ↦ h.elim hj0 hj1)] at hcoord
      exact hcoord
    simp [hj]

/-- Helper for Remark 5.18: the `ℓ₁` distance between two distinct simplex vertices is `2`. -/
lemma l1Norm_twoVertexDifference
    (i0 i1 : Fin n) (h01 : i0 ≠ i1) :
    ‖(PiLp.single 1 i0 (1 : ℝ) : E₁) - (PiLp.single 1 i1 (1 : ℝ) : E₁)‖ = 2 := by
  let d : E₁ := (PiLp.single 1 i0 (1 : ℝ) : E₁) - (PiLp.single 1 i1 (1 : ℝ) : E₁)
  rw [show
      ‖(PiLp.single 1 i0 (1 : ℝ) : E₁) - (PiLp.single 1 i1 (1 : ℝ) : E₁)‖ = ‖d‖ by rfl]
  rw [PiLp.norm_eq_of_L1]
  -- The coordinate formula shows that only the two distinguished entries contribute.
  have hsplit :
      (∑ j : Fin n, ‖d.ofLp j‖) =
        Finset.sum (Finset.univ.erase i0) (fun j ↦ ‖d.ofLp j‖) + ‖d.ofLp i0‖ := by
    exact
      (Finset.sum_erase_add
        (s := Finset.univ) (a := i0)
        (f := fun j : Fin n ↦ ‖d.ofLp j‖)
        (Finset.mem_univ i0)).symm
  rw [hsplit]
  rw [Finset.sum_eq_single_of_mem i1]
  · have hi0 : d i0 = 1 := by
      dsimp [d]
      simp [h01]
    have hi1 : d i1 = (-1 : ℝ) := by
      dsimp [d]
      simp [h01]
    rw [hi0, hi1]
    norm_num
  · exact Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ i1⟩
  · intro j hj hjne
    have hj0 : j ≠ i0 := (Finset.mem_erase.mp hj).1
    have hj : d j = 0 := by
      have hcoord := twoVertexDifference_apply (n := n) i0 i1 h01 j
      rw [if_neg hj0, if_neg hjne] at hcoord
      exact hcoord
    simp [hj]

/-- Helper for Remark 5.18: on a simplex with two distinct vertices, the shift with `α = 2`
violates the `2`-strong convexity inequality at the midpoint of those vertices. -/
lemma not_two_strongConvexOn_negative_entropy_sub_two_l1Square
    (hn : 1 < n) :
    ¬ StrongConvexOn Δ₁ 2
        (fun x : E₁ ↦
          (negative_entropy_on_stdSimplex n (ofLp x)).toReal - 2 * ‖x‖ ^ (2 : ℕ)) := by
  intro hstrong
  let g : E₁ → ℝ := fun x ↦
    (negative_entropy_on_stdSimplex n (ofLp x)).toReal - 2 * ‖x‖ ^ (2 : ℕ)
  have hstrong' : StrongConvexOn Δ₁ 2 g := by
    simpa [g] using hstrong
  let i0 : Fin n := ⟨0, lt_trans (by norm_num) hn⟩
  let i1 : Fin n := ⟨1, hn⟩
  let e0 : E₁ := PiLp.single 1 i0 (1 : ℝ)
  let e1 : E₁ := PiLp.single 1 i1 (1 : ℝ)
  let m : E₁ := (1 / 2 : ℝ) • e0 + (1 / 2 : ℝ) • e1
  have h01 : i0 ≠ i1 := by
    intro h
    have : (0 : ℕ) = 1 := by
      simpa [i0, i1] using congrArg Fin.val h
    norm_num at this
  have he0 : e0 ∈ Δ₁ := by
    -- The first distinguished basis vector is a simplex vertex.
    simpa [e0] using (single_mem_stdSimplex ℝ i0)
  have he1 : e1 ∈ Δ₁ := by
    -- The second distinguished basis vector is the other simplex vertex.
    simpa [e1] using (single_mem_stdSimplex ℝ i1)
  have hm : m ∈ Δ₁ := by
    -- Their midpoint stays in the simplex by convexity.
    simpa [m, e0, e1, WithLp.ofLp_add, WithLp.ofLp_smul] using
      (convex_stdSimplex (𝕜 := ℝ) (ι := Fin n)) he0 he1
        (by norm_num) (by norm_num) (by norm_num)
  have hg0 : g e0 = -2 := by
    -- On a simplex vertex, the entropy vanishes and the quadratic shift is the constant `2`.
    dsimp [g]
    rw [negative_entropy_sub_alpha_l1Square_eq_sub_alpha_of_mem_stdSimplex (n := n) 2 he0]
    rw [show
      (negative_entropy_on_stdSimplex n (ofLp e0)).toReal =
        (negative_entropy_on_stdSimplex n (Pi.single i0 (1 : ℝ))).toReal by
          simp [e0]]
    rw [entropyValue_singleVertex (n := n) i0]
    norm_num
  have hg1 : g e1 = -2 := by
    -- The same evaluation holds at the second simplex vertex.
    dsimp [g]
    rw [negative_entropy_sub_alpha_l1Square_eq_sub_alpha_of_mem_stdSimplex (n := n) 2 he1]
    rw [show
      (negative_entropy_on_stdSimplex n (ofLp e1)).toReal =
        (negative_entropy_on_stdSimplex n (Pi.single i1 (1 : ℝ))).toReal by
          simp [e1]]
    rw [entropyValue_singleVertex (n := n) i1]
    norm_num
  have hgm : g m = - Real.log 2 - 2 := by
    -- The midpoint value is the entropy midpoint `- log 2` shifted down by `2`.
    dsimp [g]
    rw [negative_entropy_sub_alpha_l1Square_eq_sub_alpha_of_mem_stdSimplex (n := n) 2 hm]
    rw [show
      (negative_entropy_on_stdSimplex n (ofLp m)).toReal =
        (negative_entropy_on_stdSimplex n
          (ofLp ((1 / 2 : ℝ) • (PiLp.single 1 i0 (1 : ℝ) : E₁) +
            (1 / 2 : ℝ) • (PiLp.single 1 i1 (1 : ℝ) : E₁)))).toReal by
          simp [m, e0, e1]]
    rw [entropyValue_twoVertexMidpoint (n := n) i0 i1 h01]
  have hdist : ‖e0 - e1‖ = 2 := by
    -- The two simplex vertices differ by `1` and `-1` on exactly two coordinates.
    simpa [e0, e1] using l1Norm_twoVertexDifference (n := n) i0 i1 h01
  -- Route correction: stay on `Fin n` and use the support lemmas above instead of reindexing
  -- through `Fin (2 + k)`.
  have hineq :
      g m ≤
        (1 / 2 : ℝ) * g e0 + (1 / 2 : ℝ) * g e1 -
          (1 / 2 : ℝ) * (1 / 2 : ℝ) * ((2 : ℝ) / 2 * ‖e0 - e1‖ ^ (2 : ℕ)) := by
    simpa [g, m, smul_eq_mul] using
      hstrong'.2 he0 he1 (by norm_num) (by norm_num) (by norm_num)
  rw [hg0, hg1, hgm, hdist] at hineq
  have hlog_ge : 1 ≤ Real.log 2 := by
    nlinarith [hineq]
  nlinarith [hlog_ge, Real.log_two_lt_d9]

-- Semantic recall: `StrongConvexOn` is the canonical owner here, and the negated universal claim
-- needs a nontrivial simplex rather than the singleton case `n = 1`.
-- Proof sketch: the preceding theorem shows that every positive shift parameter still gives a
-- convex function. If the same parameter `α` also yielded `α`-strong convexity for all `α > 0`,
-- then this one simplex entropy profile would admit arbitrarily large strong-convexity moduli up
-- to constant translation, contradicting the finite-curvature geometry alluded to in the remark.
/-- Remark 5.18: the entropy shift cannot realize the same positive parameter simultaneously as
shift size and strong-convexity modulus for every `α > 0` once the simplex has at least two
distinct points. -/
theorem not_forall_pos_strongConvexOn_negative_entropy_sub_alpha_l1Square
    (hn : 1 < n) :
    ¬ ∀ α > 0,
      StrongConvexOn Δ₁ α
        (fun x : E₁ ↦
          (negative_entropy_on_stdSimplex n (ofLp x)).toReal - α * ‖x‖ ^ (2 : ℕ)) := by
  intro hα
  -- Specialize the universal claim at `α = 2`, where the explicit midpoint obstruction applies.
  exact
    not_two_strongConvexOn_negative_entropy_sub_two_l1Square (n := n) hn
      (hα 2 (by norm_num))

end
