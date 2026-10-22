/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Text_8_0_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u

namespace ERealFunction

variable {H : Type u}

/-- The real values attained by an `]-∞,+∞]`-valued function. -/
def realRange (f : H → Set.Ioi (⊥ : EReal)) : Set ℝ :=
  ((↑) : ℝ → EReal) ⁻¹' Set.range fun x ↦ (f x : EReal)

-- Proof sketch: unfold `realRange` and the set-theoretic definition of `Set.range`.
/-- A real number belongs to `realRange f` exactly when `f` attains that real value. -/
theorem mem_realRange_iff (f : H → Set.Ioi (⊥ : EReal)) (t : ℝ) :
    t ∈ realRange f ↔ ∃ x, (f x : EReal) = t := by
  -- Unfold `realRange`; membership is exactly saying that the coerced real lies in the range.
  simp [realRange]

/-- The `EReal`-valued extension of a real `]-∞,+∞]`-valued function to `]-∞,+∞]` obtained by
sending `+∞` to `+∞`. -/
noncomputable def topExtensionEReal (φ : ℝ → Set.Ioi (⊥ : EReal)) :
    Set.Ioi (⊥ : EReal) → EReal
  | ⟨⊥, h⟩ => nomatch h
  | ⟨(r : ℝ), _⟩ => φ r
  | ⟨⊤, _⟩ => ⊤

/-- The `EReal`-valued top extension still takes values in `]-∞,+∞]`. -/
theorem topExtensionEReal_mem_Ioi_bot (φ : ℝ → Set.Ioi (⊥ : EReal))
    (x : Set.Ioi (⊥ : EReal)) :
    topExtensionEReal φ x ∈ Set.Ioi (⊥ : EReal) := by
  by_cases htop : (x : EReal) = ⊤
  · -- The top branch stays at `+∞`, which still lies in `]-∞,+∞]`.
    have hx_eq_top : x = ⟨(⊤ : EReal), top_mem_Ioi_bot⟩ := by
      apply Subtype.ext
      simpa using htop
    rw [hx_eq_top]
    change (⊤ : EReal) ∈ Set.Ioi (⊥ : EReal)
    exact top_mem_Ioi_bot
  · -- Otherwise the input is finite, so the extension reduces to the original `φ`.
    have hfinite : (x : EReal) < ⊤ := lt_of_le_of_ne le_top htop
    obtain ⟨r, rfl⟩ : ∃ r : ℝ, x = ⟨(r : EReal), EReal.bot_lt_coe r⟩ := by
      refine ⟨(x : EReal).toReal, ?_⟩
      apply Subtype.ext
      simpa using
        (EReal.coe_toReal (ne_of_lt hfinite) (ne_of_gt x.property)).symm
    change (φ r : EReal) ∈ Set.Ioi (⊥ : EReal)
    exact (φ r).property

-- Proof sketch: evaluate `topExtensionEReal` on the real branch of the defining pattern match.
/-- On finite real inputs, `topExtensionEReal φ` agrees with `φ`. -/
@[simp] theorem topExtensionEReal_apply_coe (φ : ℝ → Set.Ioi (⊥ : EReal)) (r : ℝ) :
    topExtensionEReal φ ⟨(r : EReal), EReal.bot_lt_coe r⟩ = φ r := by
  rfl

-- Proof sketch: evaluate `topExtensionEReal` on the `+∞` branch of the defining pattern match.
/-- At `+∞`, `topExtensionEReal φ` takes the value `+∞`. -/
@[simp] theorem topExtensionEReal_apply_top (φ : ℝ → Set.Ioi (⊥ : EReal)) :
    topExtensionEReal φ ⟨(⊤ : EReal), top_mem_Ioi_bot⟩ = ⊤ := by
  rfl

/-- Helper for Proposition 8.21: on the finite branch, the top extension reduces to evaluation of
`φ` at the induced real value. -/
private theorem topExtensionEReal_eq_apply_toReal_of_mem_effectiveDomain
    (φ : ℝ → Set.Ioi (⊥ : EReal)) {x : Set.Ioi (⊥ : EReal)} (hx : (x : EReal) < ⊤) :
    topExtensionEReal φ x = φ ((x : EReal).toReal) := by
  -- A finite `EReal` in `]-∞,+∞]` is represented by some real number, so the extension is on its
  -- original branch.
  obtain ⟨r, rfl⟩ : ∃ r : ℝ, x = ⟨(r : EReal), EReal.bot_lt_coe r⟩ := by
    refine ⟨(x : EReal).toReal, ?_⟩
    apply Subtype.ext
    simpa using
      (EReal.coe_toReal (ne_of_lt hx) (ne_of_gt x.property)).symm
  rfl

/-- Helper for Proposition 8.21: the composition with the top extension is finite exactly when the
inner value is finite and the corresponding real value lies in the effective domain of `φ`. -/
private theorem mem_dom_comp_topExtension_iff
    (f : H → Set.Ioi (⊥ : EReal)) (φ : ℝ → Set.Ioi (⊥ : EReal)) (x : H) :
    x ∈ dom (fun z : H ↦ topExtensionEReal φ (f z)) ↔
      x ∈ effectiveDomain f ∧ ((f x : EReal).toReal ∈ effectiveDomain φ) := by
  constructor
  · intro hx
    -- Domain membership of the composition rules out the `+∞` branch of `f x`.
    have hcomp_finite : topExtensionEReal φ (f x) < ⊤ := by
      simpa [dom] using hx
    have hfx_ne_top : (f x : EReal) ≠ ⊤ := by
      intro hfx_top
      have hfx_eq_top : f x = ⟨(⊤ : EReal), top_mem_Ioi_bot⟩ := by
        apply Subtype.ext
        simpa using hfx_top
      rw [hfx_eq_top, topExtensionEReal_apply_top] at hcomp_finite
      exact not_top_lt hcomp_finite
    have hfx_finite : (f x : EReal) < ⊤ := by
      exact lt_of_le_of_lt (EReal.le_coe_toReal hfx_ne_top) (EReal.coe_lt_top ((f x : EReal).toReal))
    have hφ_finite : (φ ((f x : EReal).toReal) : EReal) < ⊤ := by
      rw [topExtensionEReal_eq_apply_toReal_of_mem_effectiveDomain (φ := φ) hfx_finite] at hcomp_finite
      exact hcomp_finite
    exact ⟨by simpa [effectiveDomain] using hfx_finite, by
      simpa [effectiveDomain] using hφ_finite⟩
  · rintro ⟨hfx_dom, hφ_dom⟩
    -- On the finite branch of `f x`, the top extension is just `φ` evaluated at `toReal`.
    have hfx_finite : (f x : EReal) < ⊤ := by
      simpa [effectiveDomain] using hfx_dom
    rw [mem_dom_iff]
    rw [topExtensionEReal_eq_apply_toReal_of_mem_effectiveDomain (φ := φ) hfx_finite]
    simpa [effectiveDomain] using hφ_dom

section RealVectorSpace

variable [AddCommGroup H] [Module ℝ H]

-- Proof sketch: use Proposition 8.4 to reduce convexity of the composition to Jensen's
-- inequality on its effective domain. For `x` and `y` in the domain of the composition, the values
-- `f x` and `f y` are finite real points of `realRange f`, hence their convex combinations lie in
-- `convexHull ℝ (realRange f)`. Apply convexity of `f`, monotonicity of `φ` on that convex hull,
-- and then convexity of `φ` to obtain the Jensen inequality for `topExtensionEReal φ ∘ f`.
/-- Proposition 8.21: let `f : 𝓗 → ]-∞,+∞]` and `φ : ℝ → ]-∞,+∞]`. If `f` has convex epigraph,
`φ` has convex epigraph on `ℝ`, every point of the convex hull of the real values attained by `f`
lies in the effective domain of `φ`, and `φ` is increasing on that convex hull, then the
composition of `f` with the extension of `φ` sending `+∞` to `+∞` again has convex epigraph. -/
theorem convex_epigraph_comp_topExtension
    (f : H → Set.Ioi (⊥ : EReal)) (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hf : Convex ℝ (epigraph fun x : H ↦ (f x : EReal)))
    (hφ : Convex ℝ (epigraph fun t : ℝ ↦ (φ t : EReal)))
    (hdom : convexHull ℝ (realRange f) ⊆ effectiveDomain φ)
    (hmono : MonotoneOn (fun t ↦ (φ t : EReal)) (convexHull ℝ (realRange f))) :
    Convex ℝ (epigraph fun x : H ↦ topExtensionEReal φ (f x)) := by
  refine (convex_epigraph_iff_jensen_on_dom _).2 ?_
  intro x y hx hy α hα hα_lt_one
  -- Decode the domain of the composition into finiteness of `f` and domain membership for `φ`.
  rcases (mem_dom_comp_topExtension_iff f φ x).1 hx with ⟨hx_fdom, hx_φdom⟩
  rcases (mem_dom_comp_topExtension_iff f φ y).1 hy with ⟨hy_fdom, hy_φdom⟩
  let tx : ℝ := (f x : EReal).toReal
  let ty : ℝ := (f y : EReal).toReal
  let z : H := α • x + (1 - α) • y
  let tz : ℝ := (f z : EReal).toReal
  let s : ℝ := α * tx + (1 - α) * ty
  have hx_finite : (f x : EReal) < ⊤ := by
    simpa [effectiveDomain] using hx_fdom
  have hy_finite : (f y : EReal) < ⊤ := by
    simpa [effectiveDomain] using hy_fdom
  have htx :
      ((tx : ℝ) : EReal) = (f x : EReal) := by
    simpa [tx] using
      (EReal.coe_toReal (ne_of_lt hx_finite) (ne_of_gt (f x).property))
  have hty :
      ((ty : ℝ) : EReal) = (f y : EReal) := by
    simpa [ty] using
      (EReal.coe_toReal (ne_of_lt hy_finite) (ne_of_gt (f y).property))
  have hgx : topExtensionEReal φ (f x) = φ tx := by
    -- The endpoint `x` lies on the finite branch of `f`.
    simpa [tx] using
      topExtensionEReal_eq_apply_toReal_of_mem_effectiveDomain (φ := φ) (x := f x) hx_finite
  have hgy : topExtensionEReal φ (f y) = φ ty := by
    -- The endpoint `y` lies on the finite branch of `f`.
    simpa [ty] using
      topExtensionEReal_eq_apply_toReal_of_mem_effectiveDomain (φ := φ) (x := f y) hy_finite
  have hxφ_dom : tx ∈ dom (fun t : ℝ ↦ (φ t : EReal)) := by
    simpa [effectiveDomain, dom] using hx_φdom
  have hyφ_dom : ty ∈ dom (fun t : ℝ ↦ (φ t : EReal)) := by
    simpa [effectiveDomain, dom] using hy_φdom
  have hfJ :
      (f z : EReal) ≤ (α : EReal) * (f x : EReal) +
        (((1 - α : ℝ) : EReal) * (f y : EReal)) := by
    -- Proposition 8.4 turns convexity of `f` into the required Jensen inequality.
    have hx_dom : x ∈ dom (fun w : H ↦ (f w : EReal)) := by
      simpa [effectiveDomain, dom] using hx_fdom
    have hy_dom : y ∈ dom (fun w : H ↦ (f w : EReal)) := by
      simpa [effectiveDomain, dom] using hy_fdom
    simpa [z] using
      ((convex_epigraph_iff_jensen_on_dom (fun w : H ↦ (f w : EReal))).1 hf
        hx_dom hy_dom hα hα_lt_one)
  have hf_combo :
      (f z : EReal) ≤ (s : EReal) := by
    -- Rewrite the Jensen upper bound for `f` using the real representatives `tx` and `ty`.
    calc
      (f z : EReal)
          ≤ (α : EReal) * (f x : EReal) + (((1 - α : ℝ) : EReal) * (f y : EReal)) := hfJ
      _ = (s : EReal) := by
        rw [← htx, ← hty, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  have hz_finite : (f z : EReal) < ⊤ := by
    -- The Jensen upper bound is a real `EReal`, so the midpoint value of `f` is finite.
    exact lt_of_le_of_lt hf_combo (EReal.coe_lt_top s)
  have hgz : topExtensionEReal φ (f z) = φ tz := by
    -- The midpoint also lies on the finite branch of `f`.
    simpa [z, tz] using
      topExtensionEReal_eq_apply_toReal_of_mem_effectiveDomain (φ := φ) (x := f z) hz_finite
  have htx_range : tx ∈ realRange f := by
    -- Real endpoint values of `f` belong to the textbook set `ℝ ∩ ran f`.
    exact (mem_realRange_iff f tx).2 ⟨x, by simpa [tx] using htx.symm⟩
  have hty_range : ty ∈ realRange f := by
    exact (mem_realRange_iff f ty).2 ⟨y, by simpa [ty] using hty.symm⟩
  have htz_range : tz ∈ realRange f := by
    exact (mem_realRange_iff f tz).2 ⟨z, by
      simpa [z, tz] using
        (EReal.coe_toReal (ne_of_lt hz_finite) (ne_of_gt (f z).property)).symm⟩
  have hs_hull : s ∈ convexHull ℝ (realRange f) := by
    -- The convex hull contains convex combinations of the endpoint real values.
    have htx_hull : tx ∈ convexHull ℝ (realRange f) :=
      subset_convexHull ℝ (realRange f) htx_range
    have hty_hull : ty ∈ convexHull ℝ (realRange f) :=
      subset_convexHull ℝ (realRange f) hty_range
    have hconv_hull : Convex ℝ (convexHull ℝ (realRange f)) :=
      convex_convexHull ℝ (realRange f)
    have hα_mem : α ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hα, hα_lt_one.le⟩
    simpa [s, AffineMap.lineMap_apply_ring, add_comm, add_left_comm, add_assoc, mul_comm,
      mul_left_comm, mul_assoc] using
      hconv_hull.lineMap_mem hty_hull htx_hull hα_mem
  have htz_hull : tz ∈ convexHull ℝ (realRange f) :=
    subset_convexHull ℝ (realRange f) htz_range
  have hs_φdom : s ∈ dom (fun t : ℝ ↦ (φ t : EReal)) := by
    -- This records the textbook inclusion `C ⊆ dom φ` for the hull point `s`.
    simpa [effectiveDomain, dom] using hdom hs_hull
  have htz_le_s : tz ≤ s := by
    -- Convert the midpoint inequality for `f` into an inequality between the associated reals.
    simpa [tz, s] using
      EReal.toReal_le_toReal hf_combo (ne_of_gt (f z).property) (EReal.coe_ne_top s)
  have hmono_step : (φ tz : EReal) ≤ (φ s : EReal) := by
    -- Monotonicity on the hull transfers the inequality through `φ`.
    exact hmono htz_hull hs_hull htz_le_s
  have hφJ :
      (φ s : EReal) ≤ (α : EReal) * (φ tx : EReal) +
        (((1 - α : ℝ) : EReal) * (φ ty : EReal)) := by
    -- Proposition 8.4 applies again, now to the convex function `φ` on `ℝ`.
    simpa [s, smul_eq_mul] using
      ((convex_epigraph_iff_jensen_on_dom (fun t : ℝ ↦ (φ t : EReal))).1 hφ
        hxφ_dom hyφ_dom hα hα_lt_one)
  have hs_φfinite : (φ s : EReal) < ⊤ := by
    simpa [dom] using hs_φdom
  -- Combine the convexity estimate for `f`, monotonicity of `φ` on the hull, and convexity of `φ`.
  calc
    topExtensionEReal φ (f (α • x + (1 - α) • y))
        = φ tz := by simpa [z] using hgz
    _ ≤ (φ s : EReal) := hmono_step
    _ ≤ (α : EReal) * (φ tx : EReal) + (((1 - α : ℝ) : EReal) * (φ ty : EReal)) := hφJ
    _ = (α : EReal) * topExtensionEReal φ (f x) +
          (((1 - α : ℝ) : EReal) * topExtensionEReal φ (f y)) := by
        rw [hgx, hgy]

end RealVectorSpace

end ERealFunction
