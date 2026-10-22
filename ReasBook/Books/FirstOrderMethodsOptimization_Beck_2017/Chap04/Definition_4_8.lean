/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 4.8 is `source-facing`: the split equality-constrained Lagrangian and the dual
value of that split problem are the chapter's source-level objects. The `core/canonical` owner
for Fenchel conjugates remains `conjugate_function` from Definition 4.1, so the only primitive
data introduced here is the split Lagrangian together with the resulting dual objective
`fenchel_dual_objective`; the infimum presentation and the dual-problem value are derived
`bridge/view` API. -/

/-- The Lagrangian of the split equality-constrained formulation
`min_{x,z} {f x + g z : x = z}` with dual variable `y ∈ E*`. -/
def fenchel_split_lagrangian
    (f g : E → EReal) (x z : E) (y : Module.Dual ℝ E) : EReal :=
  f x + g z + (y (z - x) : EReal)

-- Proof sketch: unfold `fenchel_split_lagrangian`; this is exactly its defining formula.
/-- Evaluating the split Lagrangian gives the split objective plus the dual pairing of the equality
constraint residual `z - x`. -/
@[simp] theorem fenchel_split_lagrangian_apply
    (f g : E → EReal) (x z : E) (y : Module.Dual ℝ E) :
    fenchel_split_lagrangian f g x z y = f x + g z + (y (z - x) : EReal) := rfl

-- Proof sketch: expand `y (z - x)` by linearity as `y z - y x`, then regroup the resulting
-- extended-real terms into the two bracketed affine pieces from equation (4.4.3).
/-- The split Lagrangian rewrites as the negative of the two affine-conjugate integrands appearing
in equation (4.4.3). -/
theorem fenchel_split_lagrangian_eq_neg_conjugate_integrands
    (f g : E → EReal) (x z : E) (y : Module.Dual ℝ E) :
    fenchel_split_lagrangian f g x z y =
      -((y x : EReal) - f x) - (((-y) z : EReal) - g z) := by
  have hx : -((y x : EReal) - f x) = f x - (y x : EReal) := by
    rw [EReal.neg_sub] <;> simp [sub_eq_add_neg, add_comm]
  have hz : -((((-y) z : EReal) - g z)) = g z - (((-y) z : EReal)) := by
    rw [EReal.neg_sub] <;> simp [sub_eq_add_neg, add_comm]
  have hy : (y (z - x) : EReal) = ((y z - y x : ℝ) : EReal) := by
    simp [map_sub]
  calc
    fenchel_split_lagrangian f g x z y = f x + g z + (y (z - x) : EReal) := by
      rw [fenchel_split_lagrangian_apply]
    _ = f x + g z + ((y z - y x : ℝ) : EReal) := by
      rw [hy]
    _ = f x - (y x : EReal) + (g z - (((-y) z : EReal))) := by
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = -((y x : EReal) - f x) - (((-y) z : EReal) - g z) := by
      rw [← hx, ← hz, ← sub_eq_add_neg]

/-- The dual objective function from Definition 4.8 for the primal problem
`min_x (f x + g x)`, equivalently for the split problem `min_{x,z} {f x + g z : x = z}`, is
Fenchel's dual objective `q(y) = -f*(y) - g*(-y)`, written using the Chapter 4 owner
`conjugate_function` for the conjugates of `f` and `g`. -/
def fenchel_dual_objective (f g : E → EReal) : Module.Dual ℝ E → EReal :=
  fun y ↦ -conjugate_function f y - conjugate_function g (-y)

-- Proof sketch: unfold `fenchel_dual_objective`; the statement is exactly the defining formula of
-- Fenchel's dual objective at the dual vector `y`.
/-- Evaluating Fenchel's dual objective at `y` gives `-f*(y) - g*(-y)`. -/
@[simp] theorem fenchel_dual_objective_apply (f g : E → EReal) (y : Module.Dual ℝ E) :
    fenchel_dual_objective f g y = -conjugate_function f y - conjugate_function g (-y) := rfl

/-- Helper for Definition 4.8: the sum of two indexed suprema in `EReal` is the supremum over
the product index of the pointwise sums. -/
lemma ereal_iSup_add_eq_iSup_prod {α β : Type*} (u : α → EReal) (v : β → EReal) :
    (⨆ a, u a) + ⨆ b, v b = ⨆ p : α × β, u p.1 + v p.2 := by
  refine le_antisymm ?_ ?_
  · -- Approximate each supremum from below and combine the two witnesses into one product index.
    refine EReal.add_le_of_forall_lt ?_
    intro a ha b hb
    rcases lt_iSup_iff.mp ha with ⟨i, hi⟩
    rcases lt_iSup_iff.mp hb with ⟨j, hj⟩
    exact (add_le_add hi.le hj.le).trans (le_iSup_of_le (i, j) le_rfl)
  · -- The opposite inequality is the pointwise monotonicity of addition under each `iSup`.
    refine iSup_le ?_
    intro p
    exact add_le_add (le_iSup u p.1) (le_iSup v p.2)

/-- Helper for Definition 4.8: negating a set of extended-real values turns its infimum into the
negated supremum. -/
lemma ereal_sInf_neg (s : Set EReal) :
    sInf (-s) = -sSup s := by
  -- Compare both sides by translating lower and upper bounds through negation.
  refine le_antisymm ?_ ?_
  · have hsSup : sSup s ≤ -sInf (-s) := by
      refine sSup_le fun x hx ↦ ?_
      have hsInf : sInf (-s) ≤ -x := by
        exact sInf_le (by simpa [Set.mem_neg] using hx : -x ∈ -s)
      exact EReal.le_neg.mp hsInf
    exact EReal.le_neg.mpr hsSup
  · refine le_sInf fun z hz ↦ ?_
    exact EReal.neg_le.mpr (le_sSup (by simpa [Set.mem_neg] using hz : -z ∈ s))

/-- Helper for Definition 4.8: for a proper function, each affine perturbation
`(y x : EReal) - f x` stays away from `⊤`. -/
lemma affinePairingMinusValue_ne_top_of_proper
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (y : Module.Dual ℝ E) (x : E) :
    ((y x : EReal) - f x) ≠ ⊤ := by
  by_cases hfx_top : f x = ⊤
  · -- If `f x = ⊤`, the affine perturbation is `⊥`, so it certainly is not `⊤`.
    simp [hfx_top]
  · -- Otherwise `f x` is finite because properness already rules out `⊥`.
    lift f x to ℝ using ⟨hfx_top, hf_proper.ne_bot x⟩ with fx hfx
    simpa [← hfx, EReal.coe_sub] using (EReal.coe_ne_top (y x - fx))

/-- Helper for Definition 4.8: a proper function has a conjugate that never takes the value
`⊥`. -/
lemma conjugate_function_ne_bot_of_proper
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f) (y : Module.Dual ℝ E) :
    conjugate_function f y ≠ ⊥ := by
  rcases hf_proper.effective_domain_nonempty with ⟨z, hz⟩
  have hz_term : ((y z : EReal) - f z) ≤ conjugate_function f y := by
    -- Evaluate the defining supremum at one finite point in the effective domain.
    rw [conjugate_function_apply]
    exact le_sSup (Set.mem_range_self z)
  have hfz_top : f z ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hz)
  lift f z to ℝ using ⟨hfz_top, hf_proper.ne_bot z⟩ with fz hfz
  have hz_term' : ((y z : EReal) - (fz : EReal)) ≤ conjugate_function f y := by
    simpa [← hfz] using hz_term
  have hz_term_ne_bot : ((y z : EReal) - f z) ≠ ⊥ := by
    -- The chosen affine perturbation is a finite real value after lifting `f z`.
    simpa [← hfz, EReal.coe_sub] using EReal.coe_ne_bot (y z - fz)
  -- One finite point in the supremum range prevents the conjugate from collapsing to `⊥`.
  exact bot_lt_iff_ne_bot.mp
    ((bot_lt_iff_ne_bot.mpr hz_term_ne_bot).trans_le (by simpa [← hfz] using hz_term'))

/-- Helper for Definition 4.8: the split Lagrangian range is the negated range of the separable
sum of the two affine-conjugate integrands from equation `(4.4.3)`. -/
lemma fenchel_split_lagrangian_range_eq_neg_integrand_range
    (f g : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hg_proper : IsProperExtendedRealFunction g) (y : Module.Dual ℝ E) :
    Set.range (fun xz : E × E ↦ fenchel_split_lagrangian f g xz.1 xz.2 y) =
      -Set.range
        (fun xz : E × E ↦ ((y xz.1 : EReal) - f xz.1) + (((-y) xz.2 : EReal) - g xz.2)) := by
  ext w
  constructor
  · rintro ⟨⟨x, z⟩, rfl⟩
    rw [Set.mem_neg]
    refine ⟨(x, z), ?_⟩
    have hx_ne_top : ((y x : EReal) - f x) ≠ ⊤ :=
      affinePairingMinusValue_ne_top_of_proper f hf_proper y x
    have hz_ne_top : (((-y) z : EReal) - g z) ≠ ⊤ :=
      affinePairingMinusValue_ne_top_of_proper g hg_proper (-y) z
    have hsplit :
        fenchel_split_lagrangian f g x z y =
          -(((y x : EReal) - f x) + (((-y) z : EReal) - g z)) := by
      -- Combine the two negated affine pieces into one negated sum.
      rw [fenchel_split_lagrangian_eq_neg_conjugate_integrands]
      rw [(EReal.neg_add (.inr hz_ne_top) (.inl hx_ne_top)).symm]
    calc
      ((y x : EReal) - f x) + (((-y) z : EReal) - g z)
          = -(-(((y x : EReal) - f x) + (((-y) z : EReal) - g z))) := by
              simp
      _ = -fenchel_split_lagrangian f g x z y := by
              rw [hsplit]
  · rw [Set.mem_neg]
    rintro ⟨⟨x, z⟩, hw⟩
    refine ⟨(x, z), ?_⟩
    have hx_ne_top : ((y x : EReal) - f x) ≠ ⊤ :=
      affinePairingMinusValue_ne_top_of_proper f hf_proper y x
    have hz_ne_top : (((-y) z : EReal) - g z) ≠ ⊤ :=
      affinePairingMinusValue_ne_top_of_proper g hg_proper (-y) z
    have hsplit :
        fenchel_split_lagrangian f g x z y =
          -(((y x : EReal) - f x) + (((-y) z : EReal) - g z)) := by
      -- Reuse the same normalization in the reverse membership direction.
      rw [fenchel_split_lagrangian_eq_neg_conjugate_integrands]
      rw [(EReal.neg_add (.inr hz_ne_top) (.inl hx_ne_top)).symm]
    have hw' : w = fenchel_split_lagrangian f g x z y := by
      -- Negating the witness identity recovers the original Lagrangian value.
      calc
        w = -(-w) := by simp
        _ = -(((y x : EReal) - f x) + (((-y) z : EReal) - g z)) := by rw [← hw]
        _ = fenchel_split_lagrangian f g x z y := by rw [hsplit]
    exact hw'.symm

-- Proof sketch: under properness of `f` and `g`, rewrite `fenchel_split_lagrangian` with
-- `fenchel_split_lagrangian_eq_neg_conjugate_integrands`, separate the infimum over the product
-- variables into the `x`- and `z`-parts, and identify those two order-theoretic infima with the
-- negatives of `conjugate_function f y` and `conjugate_function g (-y)`.
-- Route correction: with unrestricted `EReal`-valued data this bridge is false. A verified
-- counterexample is `E = ℝ`, `f ≡ 0`, `g ≡ ⊤`, `y = LinearMap.id`, where the dual objective is
-- `⊥` but the split-Lagrangian range is constantly `⊤`.
/-- Definition 4.8: for proper extended-real-valued functions, the dual objective is the infimum
form `q(y) = inf_{x,z} L(x, z; y)` of the split Lagrangian. -/
theorem fenchel_dual_objective_eq_sInf_split_lagrangian
    (f g : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hg_proper : IsProperExtendedRealFunction g) (y : Module.Dual ℝ E) :
    fenchel_dual_objective f g y =
      sInf (Set.range fun xz : E × E ↦ fenchel_split_lagrangian f g xz.1 xz.2 y) := by
  let ψ : E × E → EReal :=
    fun xz ↦ ((y xz.1 : EReal) - f xz.1) + (((-y) xz.2 : EReal) - g xz.2)
  have hrange :
      Set.range (fun xz : E × E ↦ fenchel_split_lagrangian f g xz.1 xz.2 y) = -Set.range ψ := by
    -- Normalize the Lagrangian range once so the main proof can stay at the order-theoretic API.
    simpa [ψ] using fenchel_split_lagrangian_range_eq_neg_integrand_range f g hf_proper hg_proper y
  have hf_conj_ne_bot : conjugate_function f y ≠ ⊥ :=
    conjugate_function_ne_bot_of_proper f hf_proper y
  have hg_conj_ne_bot : conjugate_function g (-y) ≠ ⊥ :=
    conjugate_function_ne_bot_of_proper g hg_proper (-y)
  -- Rewrite the split infimum as the negation of a separable supremum problem.
  calc
    fenchel_dual_objective f g y
        = -(conjugate_function f y + conjugate_function g (-y)) := by
            rw [fenchel_dual_objective_apply]
            rw [(EReal.neg_add (.inl hf_conj_ne_bot) (.inr hg_conj_ne_bot)).symm]
    _ = -(sSup (Set.range fun x : E ↦ (y x : EReal) - f x) +
          sSup (Set.range fun z : E ↦ (((-y) z : EReal) - g z))) := by
            rw [conjugate_function_apply, conjugate_function_apply]
    _ = -((⨆ x : E, (y x : EReal) - f x) + ⨆ z : E, (((-y) z : EReal) - g z)) := by
            rw [sSup_range, sSup_range]
    _ = -(⨆ xz : E × E, ψ xz) := by
            rw [ereal_iSup_add_eq_iSup_prod]
    _ = -sSup (Set.range ψ) := by
            rw [← sSup_range]
    _ = sInf (-Set.range ψ) := by
            simpa using (ereal_sInf_neg (Set.range ψ)).symm
    _ = sInf (Set.range fun xz : E × E ↦ fenchel_split_lagrangian f g xz.1 xz.2 y) := by
            rw [← hrange]

/-- The value of Fenchel's dual problem `(D)` is the supremum of the dual objective over the dual
space `E*`. -/
def fenchel_dual_problem_value (f g : E → EReal) : EReal :=
  sSup (Set.range (fenchel_dual_objective f g))

-- Proof sketch: unfold `fenchel_dual_problem_value`; the displayed supremum over the range of the
-- dual objective is exactly the defining formula for the dual maximization problem.
/-- The dual problem value is the `EReal` supremum of the range of `fenchel_dual_objective`. -/
@[simp] theorem fenchel_dual_problem_value_eq_sSup (f g : E → EReal) :
    fenchel_dual_problem_value f g = sSup (Set.range (fenchel_dual_objective f g)) := rfl

end
