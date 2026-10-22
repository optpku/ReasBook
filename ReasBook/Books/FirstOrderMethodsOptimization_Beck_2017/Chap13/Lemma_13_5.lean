/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Text_13_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (f g : E → EReal)

/- Lemma 13.5 is a `bridge/view` item in the Chapter 13 generalized conditional-gradient domain.
Domain sampling of the surrounding owner APIs shows:
- `generalized_conditional_gradient_norm` from `Text_13_2` as the Chapter 13 owner of `S(x)`;
- `generalized_conditional_gradient_gap_objective_apply` from `Text_13_2` for the affine gap
  expansion;
- `gradient` / `∇` from mathlib as the core owner of the gradient on real Hilbert spaces;
- `conjugate_function_primal` and the notation `g∗` from `Definition_4_1` as the Chapter 4 owner
  of the Fenchel conjugate.

The primitive data here is only `f`, `g`, and `x : E`. The affine-plus-conjugate expression is
derived API, so the statement should use the existing owners directly rather than the redundant
`effective_domain f` wrapper. -/

local notation "f₀" => fun y ↦ EReal.toReal (f y)

/-- Helper for Lemma 13.5: the generalized conditional-gradient gap integrand splits into the
`x`-dependent affine term and the residual conjugate integrand. -/
private lemma generalized_conditional_gradient_gap_integrand_eq_affine_add_conjugate_integrand
    (x p : E) :
    ((inner ℝ (∇ f₀ x) (x - p) : ℝ) : EReal) + g x - g p =
      (((inner ℝ (∇ f₀ x) x : ℝ) : EReal) + g x) +
        (((inner ℝ (-∇ f₀ x) p : ℝ) : EReal) - g p) := by
  -- Rewrite the gap inner product as the affine value at `x` plus the residual linear term in
  -- `p`, matching the textbook conjugate integrand.
  have hinner :
      inner ℝ (∇ f₀ x) (x - p) =
        inner ℝ (∇ f₀ x) x + inner ℝ (-∇ f₀ x) p := by
    rw [inner_sub_right, inner_neg_left, sub_eq_add_neg]
  -- Move the finite real sum into `EReal` and regroup the extended-real additions.
  calc
    ((inner ℝ (∇ f₀ x) (x - p) : ℝ) : EReal) + g x - g p =
      (((inner ℝ (∇ f₀ x) x + inner ℝ (-∇ f₀ x) p : ℝ) : EReal) + g x) - g p := by
        rw [hinner]
    _ =
      ((((inner ℝ (∇ f₀ x) x : ℝ) : EReal) +
          ((inner ℝ (-∇ f₀ x) p : ℝ) : EReal)) + g x) - g p := by
        rw [EReal.coe_add]
    _ =
      (((inner ℝ (∇ f₀ x) x : ℝ) : EReal) + g x) +
        (((inner ℝ (-∇ f₀ x) p : ℝ) : EReal) - g p) := by
        simp only [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 13.5: the gap-integrand range is the affine shift of the conjugate-integrand
range. -/
private lemma generalized_conditional_gradient_gap_range_eq_affine_shift
    (x : E) :
    Set.range (fun p ↦ ((inner ℝ (∇ f₀ x) (x - p) : ℝ) : EReal) + g x - g p) =
      (fun z : EReal ↦ (((inner ℝ (∇ f₀ x) x : ℝ) : EReal) + g x) + z) ''
        Set.range (fun p ↦ ((inner ℝ (-∇ f₀ x) p : ℝ) : EReal) - g p) := by
  -- Upgrade the pointwise algebraic split to an equality of the corresponding ranges.
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨_, ⟨p, rfl⟩, ?_⟩
    exact generalized_conditional_gradient_gap_integrand_eq_affine_add_conjugate_integrand
      f g x p |>.symm
  · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
    refine ⟨p, ?_⟩
    exact generalized_conditional_gradient_gap_integrand_eq_affine_add_conjugate_integrand
      f g x p

/-- Helper for Lemma 13.5: taking the supremum of an affine translate of a set of extended reals
adds the same affine constant to the supremum. -/
private lemma ereal_sSup_affine_shift (c : EReal) (s : Set EReal) :
    sSup ((fun z : EReal ↦ c + z) '' s) = c + sSup s := by
  -- Handle the three shapes of the translating constant separately: bottom, finite real, and top.
  induction c with
  | bot =>
      simp
  | coe r =>
      have hrbot : (r : EReal) ≠ ⊥ := by
        simp
      have hrtop : (r : EReal) ≠ ⊤ := by
        simp
      have hgc :
          GaloisConnection (fun z : EReal ↦ (r : EReal) + z) (fun z : EReal ↦ z - r) := by
        intro a b
        constructor
        · intro hab
          exact (EReal.le_sub_iff_add_le (.inl hrbot) (.inl hrtop)).2
            (by simpa [add_comm] using hab)
        · intro hab
          have hab' := (EReal.le_sub_iff_add_le (.inl hrbot) (.inl hrtop)).1 hab
          simpa [add_comm] using hab'
      calc
        sSup ((fun z : EReal ↦ (r : EReal) + z) '' s) = ⨆ a ∈ s, (r : EReal) + a := by
          rw [sSup_image]
        _ = (r : EReal) + sSup s := by
          simpa using
            (hgc.l_sSup :
              (r : EReal) + sSup s = ⨆ a ∈ s, (r : EReal) + a).symm
  | top =>
      by_cases hs : sSup s = ⊥
      · apply le_antisymm
        · refine sSup_le ?_
          rintro _ ⟨z, hz, rfl⟩
          have hzbot : z = ⊥ := by
            have hzle : z ≤ sSup s := le_sSup hz
            rwa [hs, le_bot_iff] at hzle
          simp [hzbot]
        · simp [hs]
      · have hex : ∃ z ∈ s, z ≠ ⊥ := by
          by_contra h
          apply hs
          apply le_antisymm
          · refine sSup_le ?_
            intro z hz
            by_cases hzbot : z = ⊥
            · simp [hzbot]
            · exact False.elim (h ⟨z, hz, hzbot⟩)
          · exact bot_le
        rcases hex with ⟨z, hz, hzbot⟩
        have htop : (⊤ : EReal) ∈ ((fun z : EReal ↦ ⊤ + z) '' s) := by
          refine ⟨z, hz, ?_⟩
          simp [EReal.top_add_of_ne_bot hzbot]
        have hsTop : (⊤ : EReal) + sSup s = ⊤ := by
          simp [EReal.top_add_of_ne_bot hs]
        rw [hsTop]
        apply le_antisymm
        · exact le_top
        · exact le_sSup htop

/-- Lemma 13.5: the generalized conditional-gradient norm rewrites as the affine term
`⟪∇ f(x), x⟫ + g(x)` plus the Fenchel conjugate value `g∗(-∇ f(x))`, where the gradient is taken
for the real-valued map `y ↦ (f y).toReal`. -/
-- Proof sketch: expand `generalized_conditional_gradient_norm` as the supremum of the gap
-- objective from Text 13.2, then rewrite
-- `⟪∇f₀(x), x - p⟫ + g(x) - g(p)` as
-- `⟪∇f₀(x), x⟫ + g(x) + (⟪-∇f₀(x), p⟫ - g(p))`. The remaining supremum is exactly the Chapter 4
-- conjugate `g∗ (-∇f(x))`.
theorem generalized_conditional_gradient_norm_eq_inner_add_value_add_conjugate
    (x : E) :
    S[f₀, g](x) =
      ((inner ℝ (∇ f₀ x) x : ℝ) : EReal) +
        g x +
          (g∗) (-∇ f₀ x) := by
  -- Expand `S[f₀, g](x)` as the supremum of the explicit gap integrand from Text 13.2.
  rw [generalized_conditional_gradient_norm_eq_sSup_inner_sub_add_sub]
  have hconj :
      sSup (Set.range (fun p : E ↦ ((inner ℝ (-∇ f₀ x) p : ℝ) : EReal) - g p)) =
        (g∗) (-∇ f₀ x) := by
    -- Rewrite the Chapter 4 primal conjugate and identify the Riesz pairing with the inner
    -- product against `-∇ f₀ x`.
    rw [conjugate_function_primal_apply, conjugate_function_apply]
    apply congrArg sSup
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨p, ?_⟩
      simp [InnerProductSpace.toDualMap_apply_apply]
    · rintro ⟨p, rfl⟩
      refine ⟨p, ?_⟩
      simp [InnerProductSpace.toDualMap_apply_apply]
  -- Split off the constant affine part and recognize the remaining supremum as the conjugate.
  calc
    sSup (Set.range (fun p ↦ ((inner ℝ (∇ f₀ x) (x - p) : ℝ) : EReal) + g x - g p)) =
      sSup ((fun z : EReal ↦ (((inner ℝ (∇ f₀ x) x : ℝ) : EReal) + g x) + z) ''
        Set.range (fun p ↦ ((inner ℝ (-∇ f₀ x) p : ℝ) : EReal) - g p)) := by
        rw [generalized_conditional_gradient_gap_range_eq_affine_shift f g x]
    _ =
      (((inner ℝ (∇ f₀ x) x : ℝ) : EReal) + g x) +
        sSup (Set.range (fun p ↦ ((inner ℝ (-∇ f₀ x) p : ℝ) : EReal) - g p)) := by
        rw [ereal_sSup_affine_shift]
    _ = ((inner ℝ (∇ f₀ x) x : ℝ) : EReal) + g x + (g∗) (-∇ f₀ x) := by
        rw [hconj]

end
